/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package uefiprotocol;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import javax.swing.JFileChooser;

import ghidra.app.decompiler.ClangFieldToken;
import ghidra.app.decompiler.ClangNode;
import ghidra.app.decompiler.ClangTokenGroup;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.Pointer;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.util.task.TaskMonitor;
import docking.ActionContext;
import docking.action.DockingAction;
import docking.action.MenuData;
import docking.widgets.dialogs.InputDialog;
import ghidra.MiscellaneousPluginPackage;
import ghidra.app.plugin.PluginCategoryNames;
import ghidra.app.plugin.ProgramPlugin;
import ghidra.app.services.ConsoleService;
import ghidra.app.services.ProgramManager;
import ghidra.framework.model.Project;
import ghidra.framework.plugintool.PluginInfo;
import ghidra.framework.plugintool.PluginTool;
import ghidra.framework.plugintool.util.PluginStatus;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressIterator;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolIterator;
import ghidra.program.model.symbol.SymbolType;
import ghidra.util.Msg;

/**
 * A Ghidra Plugin that adds a menu item to search for all calls
 * to a specific function and outputs the results to the Ghidra console.
 */
@PluginInfo(
    status = PluginStatus.RELEASED,
    packageName = MiscellaneousPluginPackage.NAME,
    category = PluginCategoryNames.SEARCH,
    shortDescription = "Find calls to a function",
    description = "Adds a menu action to find all calls to a specified function name in the current program."
)
public class uefiProtocolPlugin extends ProgramPlugin {

    /**
     * Holds information about a single protocol call site, including the resolved GUID
     * passed as the protocol parameter (first arg for LocateProtocol, second for Install*).
     */
    record ProtocolCallSite(
        String programName,
        Address callSite,
        String callerFunction,
        Address guidAddress,
        String guidString
    ) {}

    enum NodeKind { PROGRAM, GUID }
    enum EdgeKind { INSTALLS, LOCATES }
    record GraphNode(String id, String label, NodeKind kind) {}
    record GraphEdge(String fromId, String toId, EdgeKind kind) {}

    /** Deduplicated, query-friendly representation of the protocol dependency graph. */
    static class ProtocolGraph {
        private final Map<String, GraphNode>   nodes        = new LinkedHashMap<>();
        private final List<GraphEdge>          edges        = new ArrayList<>();
        private final Set<String>              edgeKeys     = new LinkedHashSet<>();
        private final Map<String, String>      programIds   = new LinkedHashMap<>();
        private final Map<String, String>      guidIds      = new LinkedHashMap<>();
        private final Set<String>              installerIds = new LinkedHashSet<>();
        private final Set<String>              locatorIds   = new LinkedHashSet<>();

        private String getOrAddProgram(String name) {
            return programIds.computeIfAbsent(name, k -> {
                String id = "prog_" + programIds.size();
                nodes.put(id, new GraphNode(id, name, NodeKind.PROGRAM));
                return id;
            });
        }

        private String getOrAddGuid(String guid) {
            return guidIds.computeIfAbsent(guid, k -> {
                String id = "guid_" + guidIds.size();
                nodes.put(id, new GraphNode(id, guid, NodeKind.GUID));
                return id;
            });
        }

        void addInstall(String programName, String guid) {
            String progId = getOrAddProgram(programName);
            String guidId = getOrAddGuid(guid);
            installerIds.add(progId);
            if (edgeKeys.add("i:" + progId + ":" + guidId))
                edges.add(new GraphEdge(progId, guidId, EdgeKind.INSTALLS));
        }

        void addLocate(String programName, String guid) {
            String progId = getOrAddProgram(programName);
            String guidId = getOrAddGuid(guid);
            locatorIds.add(progId);
            if (edgeKeys.add("l:" + progId + ":" + guidId))
                edges.add(new GraphEdge(progId, guidId, EdgeKind.LOCATES));
        }

        Collection<GraphNode> getNodes()      { return nodes.values(); }
        List<GraphEdge>       getEdges()      { return edges; }
        Set<String>           getInstallerIds() { return installerIds; }
        Set<String>           getLocatorIds()   { return locatorIds; }
        boolean               isEmpty()         { return nodes.isEmpty(); }
    }

    /** Directed call graph rooted at a binary's entry point(s). */
    static class CallGraph {
        record Node(String id, String name, Address entryPoint) {}
        record Edge(String fromId, String toId) {}

        private final Map<String, Node>    nodes       = new LinkedHashMap<>();
        private final List<Edge>           edges       = new ArrayList<>();
        private final Set<String>          edgeKeys    = new LinkedHashSet<>();
        private final Map<Address, String> addressToId = new LinkedHashMap<>();

        String getOrAdd(Function func) {
            return addressToId.computeIfAbsent(func.getEntryPoint(), addr -> {
                String id = "fn_" + addressToId.size();
                nodes.put(id, new Node(id, func.getName(), addr));
                return id;
            });
        }

        void addCall(Function from, Function to) {
            String fromId = getOrAdd(from);
            String toId   = getOrAdd(to);
            if (edgeKeys.add(fromId + ":" + toId))
                edges.add(new Edge(fromId, toId));
        }

        private final Set<String>              installerNodeIds = new LinkedHashSet<>();
        private final Set<String>              locatorNodeIds   = new LinkedHashSet<>();
        private final Set<String>              entryPointIds    = new LinkedHashSet<>();
        private final Map<String, Set<String>> installerGuids   = new LinkedHashMap<>();
        private final Map<String, Set<String>> locatorGuids     = new LinkedHashMap<>();

        void tagInstaller(Address entryPoint, String guid) {
            String id = addressToId.get(entryPoint);
            if (id == null) return;
            installerNodeIds.add(id);
            if (guid != null) installerGuids.computeIfAbsent(id, k -> new LinkedHashSet<>()).add(guid);
        }

        void tagLocator(Address entryPoint, String guid) {
            String id = addressToId.get(entryPoint);
            if (id == null) return;
            locatorNodeIds.add(id);
            if (guid != null) locatorGuids.computeIfAbsent(id, k -> new LinkedHashSet<>()).add(guid);
        }

        void markEntryPoint(Address addr) {
            String id = addressToId.get(addr);
            if (id != null) entryPointIds.add(id);
        }

        void clearTags() {
            installerNodeIds.clear(); locatorNodeIds.clear();
            installerGuids.clear();   locatorGuids.clear();
        }

        Set<String> getInstallerGuids(String nodeId) {
            return installerGuids.getOrDefault(nodeId, Set.of());
        }

        Set<String> getLocatorGuids(String nodeId) {
            return locatorGuids.getOrDefault(nodeId, Set.of());
        }

        Collection<Node> getNodes()            { return nodes.values(); }
        List<Edge>       getEdges()            { return edges; }
        Set<String>      getInstallerNodeIds() { return installerNodeIds; }
        Set<String>      getLocatorNodeIds()   { return locatorNodeIds; }
        Set<String>      getEntryPointIds()    { return entryPointIds; }
        boolean          isEmpty()             { return nodes.isEmpty(); }
    }

    private DockingAction findCallsAction;
    private DockingAction locateProtocolAction;
    private DockingAction installProtocolAction;
    private DockingAction exportGraphAction;
    private DockingAction exportLocateCsvAction;
    private DockingAction exportInstallCsvAction;
    private DockingAction buildCallGraphAction;
    private DockingAction exportCallGraphAction;
    private DockingAction exportSuperCallGraphAction;
    private DockingAction runSliceAction;
    private final Map<Project, List<ProtocolCallSite>>         locateProtocolCallSites  = new HashMap<>();
    private final Map<Project, List<ProtocolCallSite>>         installProtocolCallSites = new HashMap<>();
    private final Map<Project, ProtocolGraph>                  protocolGraphs           = new HashMap<>();
    private final Map<Project, Map<String, CallGraph>>         callGraphs               = new HashMap<>();
    private final Map<Project, Map<String, String>>            sliceResults             = new HashMap<>();

    public uefiProtocolPlugin(PluginTool tool) {
        super(tool);
    }

    @Override
    protected void init() {
        super.init();
        log("[*] EFI Protocol Analyzer: plugin loaded");
        createAction();
        createLocateProtocolAction();
        createInstallProtocolAction();
        createExportGraphAction();
        createExportLocateCsvAction();
        createExportInstallCsvAction();
        createBuildCallGraphAction();
        createExportCallGraphAction();
        createExportSuperCallGraphAction();
        createRunSliceAction();
    }

    private void log(String message) {
        ConsoleService console = tool.getService(ConsoleService.class);
        if (console != null) {
            console.println(message);
        } else {
            Msg.info(this, message);
        }
    }

    private void createAction() {
        findCallsAction = new DockingAction("Find Function Calls", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                executeSearch();
            }
        };
        findCallsAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Find Function Calls..." }, null, "Search"
        ));
        tool.addAction(findCallsAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Find Function Calls...'");
    }

    private void createLocateProtocolAction() {
        locateProtocolAction = new DockingAction("List LocateProtocol Callers", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                Program[] programs = tool.getService(ProgramManager.class).getAllOpenPrograms();
                List<ProtocolCallSite> combined = new ArrayList<>();
                for (Program program : programs) {
                    // GUID is the first parameter (RCX in x86-64 UEFI calling convention)
                    combined.addAll(findViaDecompiler(program, "LocateProtocol", "RCX"));
                }
                locateProtocolCallSites.put(project, combined);
                rebuildGraph(project);
            }
        };
        locateProtocolAction.setMenuBarData(new MenuData(
            new String[] { "Search", "List LocateProtocol Callers" }, null, "Search"
        ));
        tool.addAction(locateProtocolAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > List LocateProtocol Callers'");
    }

    private void createInstallProtocolAction() {
        installProtocolAction = new DockingAction("List InstallProtocol Callers", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                Program[] programs = tool.getService(ProgramManager.class).getAllOpenPrograms();
                List<ProtocolCallSite> combined = new ArrayList<>();
                for (Program program : programs) {
                    // GUID is the second parameter (RDX in x86-64 UEFI calling convention)
                    combined.addAll(findViaDecompiler(program, "InstallProtocolInterface", "RDX"));
                    combined.addAll(findViaDecompiler(program, "InstallMultipleProtocolInterfaces", "RDX"));
                }
                installProtocolCallSites.put(project, combined);
                rebuildGraph(project);
            }
        };
        installProtocolAction.setMenuBarData(new MenuData(
            new String[] { "Search", "List InstallProtocol Callers" }, null, "Search"
        ));
        tool.addAction(installProtocolAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > List InstallProtocol Callers'");
    }

    private void executeSearch() {
        if (currentProgram == null) {
            Msg.showInfo(getClass(), null, "No Program", "Please open a program first.");
            return;
        }
        InputDialog dialog = new InputDialog("Find Function Calls", "Enter the target function name:");
        tool.showDialog(dialog);
        if (dialog.isCanceled()) {
            return;
        }
        String targetName = dialog.getValue();
        if (targetName == null || targetName.trim().isEmpty()) {
            Msg.showInfo(getClass(), null, "Invalid Input", "Please provide a valid function name.");
            return;
        }
        findAndPrintCalls(currentProgram, targetName, null);
    }

    /**
     * Finds all call sites for targetName in the given program, attempts to extract the GUID
     * from the register named guidRegister at each call site, and prints results to the console.
     *
     * @param guidRegister  register holding the GUID pointer at the call site (e.g. "RCX", "RDX"),
     *                      or null to skip GUID extraction
     */
    private List<ProtocolCallSite> findAndPrintCalls(Program program, String targetName, String guidRegister) {
        ConsoleService console = tool.getService(ConsoleService.class);
        if (console == null) {
            Msg.showError(this, null, "Error", "ConsoleService not found. Cannot print results.");
            return new ArrayList<>();
        }

        console.println("\n[*] [" + program.getName() + "] Searching for calls to: " + targetName);

        List<ProtocolCallSite> results = new ArrayList<>();

        SymbolIterator symbols = program.getSymbolTable().getSymbols(targetName);
        boolean functionFound = false;

        for (Symbol symbol : symbols) {
            functionFound = true;

            // For FUNCTION symbols use the entry point; for LABEL/DATA symbols (e.g. a
            // LocateProtocol field inside the EFI_BOOT_SERVICES struct) use the symbol address.
            Address targetAddr = (symbol.getSymbolType() == SymbolType.FUNCTION)
                ? ((Function) symbol.getObject()).getEntryPoint()
                : symbol.getAddress();

            ReferenceIterator references = program.getReferenceManager().getReferencesTo(targetAddr);

            for (Reference ref : references) {
                boolean isCallSite = ref.getReferenceType().isCall();
                if (!isCallSite) {
                    // Indirect calls (e.g. (*gBS->LocateProtocol)(...)) show up as DATA or
                    // INDIRECTION references; detect them by checking the instruction's flow type.
                    Instruction refInstr = program.getListing().getInstructionAt(ref.getFromAddress());
                    isCallSite = refInstr != null && refInstr.getFlowType().isCall();
                }
                if (!isCallSite) {
                    continue;
                }

                Address callSite = ref.getFromAddress();
                Function caller = program.getFunctionManager().getFunctionContaining(callSite);
                String callerName = (caller != null) ? caller.getName() : "Unknown/Global";

                Address guidAddr = null;
                String guidStr = null;
                if (guidRegister != null) {
                    guidAddr = extractGuidAddress(program, callSite, guidRegister);
                    if (guidAddr != null) {
                        guidStr = readGuid(program, guidAddr);
                    }
                }

                results.add(new ProtocolCallSite(program.getName(), callSite, callerName, guidAddr, guidStr));
            }
        }

        if (!functionFound) {
            console.println("[-] Symbol '" + targetName + "' not found in the symbol table.");
            return results;
        }

        if (results.isEmpty()) {
            console.println("[-] No calls found to function: " + targetName);
            return results;
        }

        console.println("[+] Found " + results.size() + " call(s) to " + targetName + ":");
        console.println("------------------------------------------------");

        for (ProtocolCallSite site : results) {
            String guidInfo = (site.guidString() != null)
                ? "  GUID: " + site.guidString() + " @ " + site.guidAddress()
                : "  GUID: <could not resolve>";
            console.println(String.format("  -> Called at %s inside '%s'", site.callSite(), site.callerFunction()));
            if (guidRegister != null) {
                console.println(guidInfo);
            }
        }

        return results;
    }

    /**
     * Uses the decompiler to find indirect calls through a named function-pointer field in a
     * typed struct, e.g. (*gBS->LocateProtocol)(...) or (*gBS->InstallProtocolInterface)(...).
     *
     * Two complementary strategies are tried for each function:
     *   1. CALLIND pcode op: the call-target varnode's type (EFI_LOCATE_PROTOCOL, etc.) is
     *      matched against fieldName by walking the PTRSUB/LOAD/CAST chain.
     *   2. ClangFieldToken fallback: if the decompiler emits a field-name token matching
     *      fieldName, we locate the nearest CALL instruction from that token's address.
     * Results are deduplicated by call-site address.
     *
     * NOTE: decompiles every function — may be slow on large binaries.
     */
    private List<ProtocolCallSite> findViaDecompiler(Program program, String fieldName, String guidRegister) {
        ConsoleService console = tool.getService(ConsoleService.class);
        if (console == null) return new ArrayList<>();

        console.println("\n[*] [" + program.getName() + "] Decompiler search for field call: " + fieldName
                + " (this may take a moment)");

        DecompInterface decompiler = new DecompInterface();
        decompiler.setOptions(new DecompileOptions());
        if (!decompiler.openProgram(program)) {
            console.println("[-] Could not open decompiler for: " + program.getName());
            return new ArrayList<>();
        }

        Set<Address> seen = new HashSet<>();
        List<ProtocolCallSite> results = new ArrayList<>();

        try {
            for (Function func : program.getFunctionManager().getFunctions(true)) {
                DecompileResults dr = decompiler.decompileFunction(func, 30, TaskMonitor.DUMMY);
                if (!dr.decompileCompleted()) continue;

                // Strategy 1: walk CALLIND pcode ops and check the call-target's type chain
                HighFunction highFunc = dr.getHighFunction();
                if (highFunc != null) {
                    Iterator<PcodeOpAST> ops = highFunc.getPcodeOps();
                    while (ops.hasNext()) {
                        PcodeOpAST op = ops.next();
                        if (op.getOpcode() != PcodeOp.CALLIND) continue;
                        if (!callTargetsField(op.getInput(0), fieldName)) continue;

                        Address callAddr = op.getSeqnum().getTarget();
                        if (seen.add(callAddr)) {
                            results.add(makeCallSite(program, callAddr, func, guidRegister));
                        }
                    }
                }

                // Strategy 2: ClangFieldToken — catches sites where type propagation is incomplete
                ClangTokenGroup markup = dr.getCCodeMarkup();
                if (markup != null) {
                    collectFieldTokenSites(program, markup, fieldName, func, guidRegister, seen, results);
                }
            }
        } finally {
            decompiler.closeProgram();
        }

        if (results.isEmpty()) {
            console.println("[-] No calls found through field: " + fieldName);
            return results;
        }

        console.println("[+] Found " + results.size() + " call(s) through " + fieldName + ":");
        console.println("------------------------------------------------");
        for (ProtocolCallSite site : results) {
            console.println(String.format("  -> Called at %s inside '%s'", site.callSite(), site.callerFunction()));
            if (guidRegister != null) {
                String guidInfo = (site.guidString() != null)
                    ? "  GUID: " + site.guidString() + " @ " + site.guidAddress()
                    : "  GUID: <could not resolve>";
                console.println(guidInfo);
            }
        }
        return results;
    }

    /**
     * Recursively walks the ClangAST looking for ClangFieldToken nodes whose text matches
     * fieldName exactly. From the token's address we scan forward up to 5 instructions for
     * the first CALL/CALLIND and record it as a call site.
     */
    private void collectFieldTokenSites(Program program, ClangNode node, String fieldName,
            Function func, String guidRegister, Set<Address> seen, List<ProtocolCallSite> results) {
        if (node instanceof ClangFieldToken ft && fieldName.equals(ft.getText())) {
            Address tokenAddr = ft.getMinAddress();
            if (tokenAddr != null) {
                Instruction instr = program.getListing().getInstructionContaining(tokenAddr);
                for (int i = 0; i < 5 && instr != null; i++) {
                    if (instr.getFlowType().isCall() && seen.add(instr.getAddress())) {
                        results.add(makeCallSite(program, instr.getAddress(), func, guidRegister));
                        break;
                    }
                    instr = instr.getNext();
                }
            }
        }
        for (int i = 0; i < node.numChildren(); i++) {
            collectFieldTokenSites(program, node.Child(i), fieldName, func, guidRegister, seen, results);
        }
    }

    /**
     * Returns true if the varnode traces back — through LOAD, PTRSUB, CAST, or COPY —
     * to a typed field whose type name contains fieldName (case-insensitive, underscore-stripped).
     *
     * For (*gBS->LocateProtocol)(args), the CALLIND's first input comes from a LOAD whose
     * source address was produced by a PTRSUB of the boot-services pointer.  The PTRSUB
     * output has type EFI_LOCATE_PROTOCOL * and the LOAD result has type EFI_LOCATE_PROTOCOL,
     * both of which match the "LocateProtocol" field name after normalization.
     */
    private boolean callTargetsField(Varnode v, String fieldName) {
        if (v == null) return false;
        if (typeMatchesField(v, fieldName)) return true;
        PcodeOp def = v.getDef();
        if (def == null) return false;
        return switch (def.getOpcode()) {
            // Recurse through the pointer address being loaded (may carry EFI_LOCATE_PROTOCOL *)
            case PcodeOp.LOAD    -> callTargetsField(def.getInput(1), fieldName);
            // PTRSUB output type is pointer-to-field (e.g. EFI_LOCATE_PROTOCOL *)
            case PcodeOp.PTRSUB  -> typeMatchesField(def.getOutput(), fieldName);
            // Transparent operations
            case PcodeOp.CAST, PcodeOp.COPY -> callTargetsField(def.getInput(0), fieldName);
            default              -> false;
        };
    }

    /** Returns true if v's high-level data type (pointer-unwrapped) contains fieldName. */
    private boolean typeMatchesField(Varnode v, String fieldName) {
        HighVariable hv = v.getHigh();
        if (hv == null) return false;
        DataType dt = hv.getDataType();
        if (dt == null) return false;
        if (dt instanceof Pointer ptr) dt = ptr.getDataType();
        if (dt == null) return false;
        String norm = dt.getName().toUpperCase().replace("_", "");
        return norm.contains(fieldName.toUpperCase().replace("_", ""));
    }

    private ProtocolCallSite makeCallSite(Program program, Address callAddr, Function func, String guidRegister) {
        Address guidAddr = null;
        String guidStr = null;
        if (guidRegister != null) {
            guidAddr = extractGuidAddress(program, callAddr, guidRegister);
            if (guidAddr != null) guidStr = readGuid(program, guidAddr);
        }
        return new ProtocolCallSite(program.getName(), callAddr, func.getName(), guidAddr, guidStr);
    }

    /**
     * Walks backwards from the call instruction to find the instruction that loads
     * guidRegister, then returns the data address it references (i.e. the GUID pointer).
     * Stops after 30 instructions or on a branch/call to avoid leaving the call's basic block.
     */
    private Address extractGuidAddress(Program program, Address callAddr, String registerName) {
        Register targetReg = program.getLanguage().getRegister(registerName);
        if (targetReg == null) {
            return null;
        }

        Instruction instr = program.getListing().getInstructionAt(callAddr);
        if (instr == null) {
            return null;
        }

        instr = instr.getPrevious();
        int limit = 30;
        while (instr != null && limit-- > 0) {
            // Stop at branches and other calls — we've left the relevant code region
            if (instr.getFlowType().isJump() || instr.getFlowType().isCall()) {
                break;
            }

            for (Object result : instr.getResultObjects()) {
                if (!(result instanceof Register resultReg)) {
                    continue;
                }
                // Match if the written register is the target or a sub-register of it
                if (!targetReg.contains(resultReg)) {
                    continue;
                }
                // Look for a data reference from this instruction (the GUID's address)
                for (Reference ref : instr.getReferencesFrom()) {
                    if (ref.getReferenceType().isData()) {
                        return ref.getToAddress();
                    }
                }
            }

            instr = instr.getPrevious();
        }

        return null;
    }

    /**
     * Reads 16 bytes from guidAddr and formats them as a standard GUID string:
     * {XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX}
     * EFI_GUID layout: uint32 Data1, uint16 Data2, uint16 Data3, uint8 Data4[8] (all little-endian).
     */
    private String readGuid(Program program, Address guidAddr) {
        byte[] bytes = new byte[16];
        try {
            program.getMemory().getBytes(guidAddr, bytes);
        } catch (MemoryAccessException e) {
            return null;
        }

        long data1 = Integer.toUnsignedLong(
            (bytes[0] & 0xFF) | ((bytes[1] & 0xFF) << 8) | ((bytes[2] & 0xFF) << 16) | ((bytes[3] & 0xFF) << 24));
        int data2 = (bytes[4] & 0xFF) | ((bytes[5] & 0xFF) << 8);
        int data3 = (bytes[6] & 0xFF) | ((bytes[7] & 0xFF) << 8);

        return String.format("{%08X-%04X-%04X-%02X%02X-%02X%02X%02X%02X%02X%02X}",
            data1, data2, data3,
            bytes[8] & 0xFF, bytes[9] & 0xFF,
            bytes[10] & 0xFF, bytes[11] & 0xFF,
            bytes[12] & 0xFF, bytes[13] & 0xFF,
            bytes[14] & 0xFF, bytes[15] & 0xFF);
    }

    private void createExportGraphAction() {
        exportGraphAction = new DockingAction("Export Protocol Graph", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                ProtocolGraph graph = protocolGraphs.get(project);
                if (graph == null || graph.isEmpty()) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'List LocateProtocol Callers' and 'List InstallProtocol Callers' first.");
                    return;
                }

                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle("Save Protocol Graph");
                chooser.setSelectedFile(new File(project.getName() + "_protocols.dot"));
                if (chooser.showSaveDialog(null) != JFileChooser.APPROVE_OPTION) {
                    return;
                }

                File file = chooser.getSelectedFile();
                try (PrintWriter pw = new PrintWriter(file)) {
                    pw.print(generateDotGraph(project.getName(), graph));
                    ConsoleService console = tool.getService(ConsoleService.class);
                    if (console != null) {
                        console.println("[+] Protocol graph written to: " + file.getAbsolutePath());
                    }
                } catch (IOException e) {
                    Msg.showError(this, null, "Export Failed", "Could not write file: " + e.getMessage());
                }
            }
        };
        exportGraphAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Export Protocol Graph..." }, null, "Search"
        ));
        tool.addAction(exportGraphAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Export Protocol Graph...'");
    }

    /** Builds the internal graph from the stored call-site lists for a project. */
    private void rebuildGraph(Project project) {
        List<ProtocolCallSite> installs = installProtocolCallSites.getOrDefault(project, List.of());
        List<ProtocolCallSite> locates  = locateProtocolCallSites.getOrDefault(project, List.of());
        ProtocolGraph graph = new ProtocolGraph();
        for (ProtocolCallSite site : installs) {
            if (site.guidString() != null) graph.addInstall(site.programName(), site.guidString());
        }
        for (ProtocolCallSite site : locates) {
            if (site.guidString() != null) graph.addLocate(site.programName(), site.guidString());
        }
        protocolGraphs.put(project, graph);
    }

    /**
     * Renders the internal ProtocolGraph as a Graphviz dot string.
     * Layout: installers on the left (rank=min), GUIDs in the middle, locators on the right
     * (rank=max). Programs that both install and locate float in between.
     * Both edge directions are kept as-is: installer → GUID (green), locator → GUID (blue).
     */
    private String generateDotGraph(String projectName, ProtocolGraph graph) {
        Set<String> leftIds  = new LinkedHashSet<>(graph.getInstallerIds());
        leftIds.removeAll(graph.getLocatorIds());
        Set<String> rightIds = new LinkedHashSet<>(graph.getLocatorIds());
        rightIds.removeAll(graph.getInstallerIds());

        StringBuilder sb = new StringBuilder();
        sb.append("digraph \"").append(escapeLabel(projectName)).append("\" {\n");
        sb.append("    rankdir=LR;\n");
        sb.append("    node [fontname=\"Helvetica\", fontsize=10];\n\n");

        if (!leftIds.isEmpty()) {
            sb.append("    { rank=min;");
            for (String id : leftIds) sb.append(" ").append(id).append(";");
            sb.append(" }\n");
        }
        if (!rightIds.isEmpty()) {
            sb.append("    { rank=max;");
            for (String id : rightIds) sb.append(" ").append(id).append(";");
            sb.append(" }\n");
        }

        sb.append("\n    // Programs\n");
        for (GraphNode n : graph.getNodes()) {
            if (n.kind() != NodeKind.PROGRAM) continue;
            sb.append("    ").append(n.id())
              .append(" [shape=box, style=filled, fillcolor=\"#AED6F1\", label=\"")
              .append(escapeLabel(n.label())).append("\"];\n");
        }

        sb.append("\n    // GUIDs\n");
        for (GraphNode n : graph.getNodes()) {
            if (n.kind() != NodeKind.GUID) continue;
            sb.append("    ").append(n.id())
              .append(" [shape=ellipse, style=filled, fillcolor=\"#A9DFBF\", label=\"")
              .append(escapeLabel(n.label())).append("\"];\n");
        }

        sb.append("\n    // installs\n");
        for (GraphEdge e : graph.getEdges()) {
            if (e.kind() != EdgeKind.INSTALLS) continue;
            sb.append("    ").append(e.fromId()).append(" -> ").append(e.toId())
              .append(" [label=\"installs\", color=\"#1E8449\", fontcolor=\"#1E8449\"];\n");
        }

        sb.append("\n    // locates\n");
        for (GraphEdge e : graph.getEdges()) {
            if (e.kind() != EdgeKind.LOCATES) continue;
            sb.append("    ").append(e.fromId()).append(" -> ").append(e.toId())
              .append(" [label=\"locates\", color=\"#2471A3\", fontcolor=\"#2471A3\"];\n");
        }

        sb.append("}\n");
        return sb.toString();
    }

    /** Escapes characters that are special inside a Graphviz double-quoted string. */
    private static String escapeLabel(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    private void createExportLocateCsvAction() {
        exportLocateCsvAction = new DockingAction("Export LocateProtocol CSV", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                List<ProtocolCallSite> sites = locateProtocolCallSites.getOrDefault(project, List.of());
                if (sites.isEmpty()) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'List LocateProtocol Callers' first.");
                    return;
                }

                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle("Save LocateProtocol CSV");
                chooser.setSelectedFile(new File(project.getName() + "_locate_protocols.csv"));
                if (chooser.showSaveDialog(null) != JFileChooser.APPROVE_OPTION) {
                    return;
                }

                File file = chooser.getSelectedFile();
                try (PrintWriter pw = new PrintWriter(file)) {
                    pw.println("program,guid");
                    Set<String> seen = new LinkedHashSet<>();
                    for (ProtocolCallSite site : sites) {
                        if (site.guidString() == null) continue;
                        String row = stripExtension(site.programName()) + "," + site.guidString();
                        if (seen.add(row)) pw.println(row);
                    }
                    ConsoleService console = tool.getService(ConsoleService.class);
                    if (console != null) {
                        console.println("[+] LocateProtocol CSV written to: " + file.getAbsolutePath());
                    }
                } catch (IOException e) {
                    Msg.showError(this, null, "Export Failed", "Could not write file: " + e.getMessage());
                }
            }
        };
        exportLocateCsvAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Export LocateProtocol CSV..." }, null, "Search"
        ));
        tool.addAction(exportLocateCsvAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Export LocateProtocol CSV...'");
    }

    private void createExportInstallCsvAction() {
        exportInstallCsvAction = new DockingAction("Export InstallProtocol CSV", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                List<ProtocolCallSite> sites = installProtocolCallSites.getOrDefault(project, List.of());
                if (sites.isEmpty()) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'List InstallProtocol Callers' first.");
                    return;
                }

                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle("Save InstallProtocol CSV");
                chooser.setSelectedFile(new File(project.getName() + "_install_protocols.csv"));
                if (chooser.showSaveDialog(null) != JFileChooser.APPROVE_OPTION) {
                    return;
                }

                File file = chooser.getSelectedFile();
                try (PrintWriter pw = new PrintWriter(file)) {
                    pw.println("program,guid");
                    Set<String> seen = new LinkedHashSet<>();
                    for (ProtocolCallSite site : sites) {
                        if (site.guidString() == null) continue;
                        String row = stripExtension(site.programName()) + "," + site.guidString();
                        if (seen.add(row)) pw.println(row);
                    }
                    ConsoleService console = tool.getService(ConsoleService.class);
                    if (console != null) {
                        console.println("[+] InstallProtocol CSV written to: " + file.getAbsolutePath());
                    }
                } catch (IOException e) {
                    Msg.showError(this, null, "Export Failed", "Could not write file: " + e.getMessage());
                }
            }
        };
        exportInstallCsvAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Export InstallProtocol CSV..." }, null, "Search"
        ));
        tool.addAction(exportInstallCsvAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Export InstallProtocol CSV...'");
    }

    private static String stripExtension(String name) {
        int dot = name.lastIndexOf('.');
        return (dot > 0) ? name.substring(0, dot) : name;
    }

    private void createBuildCallGraphAction() {
        buildCallGraphAction = new DockingAction("Build Call Graph from Entry Point", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                if (currentProgram == null) {
                    Msg.showInfo(getClass(), null, "No Program", "Please open a program first.");
                    return;
                }
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                InputDialog dialog = new InputDialog("Call Graph Depth",
                    "Max call depth (0 = unlimited):");
                tool.showDialog(dialog);
                if (dialog.isCanceled()) return;

                int maxDepth;
                try {
                    int v = Integer.parseInt(dialog.getValue().trim());
                    maxDepth = (v <= 0) ? Integer.MAX_VALUE : v;
                } catch (NumberFormatException e) {
                    Msg.showError(this, null, "Invalid Input", "Please enter a valid integer.");
                    return;
                }

                CallGraph graph = buildCallGraph(currentProgram, maxDepth);
                applyProtocolTags(currentProgram, graph, project);
                callGraphs.computeIfAbsent(project, k -> new LinkedHashMap<>())
                          .put(currentProgram.getName(), graph);

                ConsoleService console = tool.getService(ConsoleService.class);
                if (console != null) {
                    console.println(String.format(
                        "[+] [%s] Call graph: %d functions, %d edges",
                        currentProgram.getName(), graph.getNodes().size(), graph.getEdges().size()));
                }
            }
        };
        buildCallGraphAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Build Call Graph from Entry Point..." }, null, "Search"
        ));
        tool.addAction(buildCallGraphAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Build Call Graph from Entry Point...'");
    }

    private void createExportCallGraphAction() {
        exportCallGraphAction = new DockingAction("Export Call Graph", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                Map<String, CallGraph> programGraphs = callGraphs.get(project);
                String programKey = currentProgram != null ? currentProgram.getName() : null;
                CallGraph graph = (programGraphs != null && programKey != null)
                    ? programGraphs.get(programKey) : null;
                if (graph == null || graph.isEmpty()) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'Build Call Graph from Entry Point' for the current program first.");
                    return;
                }

                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle("Save Call Graph");
                chooser.setSelectedFile(new File(project.getName() + "_callgraph.dot"));
                if (chooser.showSaveDialog(null) != JFileChooser.APPROVE_OPTION) return;

                // Refresh tags in case protocol analysis ran after the graph was built
                if (currentProgram != null) applyProtocolTags(currentProgram, graph, project);

                File file = chooser.getSelectedFile();
                try (PrintWriter pw = new PrintWriter(file)) {
                    pw.print(generateCallGraphDot(currentProgram != null
                        ? currentProgram.getName() : project.getName(), graph));
                    ConsoleService console = tool.getService(ConsoleService.class);
                    if (console != null) {
                        console.println("[+] Call graph written to: " + file.getAbsolutePath());
                    }
                } catch (IOException e) {
                    Msg.showError(this, null, "Export Failed", "Could not write file: " + e.getMessage());
                }
            }
        };
        exportCallGraphAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Export Call Graph..." }, null, "Search"
        ));
        tool.addAction(exportCallGraphAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Export Call Graph...'");
    }

    /**
     * BFS from every external entry point of the program, up to maxDepth call levels deep.
     * Uses Function.getCalledFunctions() so thunks and indirect calls that Ghidra has resolved
     * are included automatically.
     */
    private CallGraph buildCallGraph(Program program, int maxDepth) {
        ConsoleService console = tool.getService(ConsoleService.class);
        if (console != null) {
            console.println("\n[*] [" + program.getName() + "] Building call graph from entry point(s)...");
        }

        CallGraph graph = new CallGraph();
        Queue<Function> queue = new ArrayDeque<>();
        Map<Address, Integer> depths = new HashMap<>();

        AddressIterator entryPoints = program.getSymbolTable().getExternalEntryPointIterator();
        while (entryPoints.hasNext()) {
            Address addr = entryPoints.next();
            Function func = program.getFunctionManager().getFunctionAt(addr);
            if (func != null && depths.putIfAbsent(addr, 0) == null) {
                graph.getOrAdd(func);
                graph.markEntryPoint(addr);
                queue.add(func);
            }
        }

        if (queue.isEmpty()) {
            if (console != null) console.println("[-] No entry points found in: " + program.getName());
            return graph;
        }

        while (!queue.isEmpty()) {
            Function current = queue.poll();
            int depth = depths.get(current.getEntryPoint());
            if (depth >= maxDepth) continue;

            for (Function callee : current.getCalledFunctions(TaskMonitor.DUMMY)) {
                graph.addCall(current, callee);
                if (depths.putIfAbsent(callee.getEntryPoint(), depth + 1) == null) {
                    queue.add(callee);
                }
            }
        }

        return graph;
    }

    /**
     * Clears and reapplies installer/locator tags on graph nodes from the stored protocol
     * call-site data.  Matching is done by address: for each call site, the function
     * containing that address is looked up and its node in the call graph is tagged.
     * Only call sites from the given program are considered.
     */
    private void applyProtocolTags(Program program, CallGraph graph, Project project) {
        graph.clearTags();
        for (ProtocolCallSite site : installProtocolCallSites.getOrDefault(project, List.of())) {
            if (!program.getName().equals(site.programName())) continue;
            Function func = program.getFunctionManager().getFunctionContaining(site.callSite());
            if (func != null) graph.tagInstaller(func.getEntryPoint(), site.guidString());
        }
        for (ProtocolCallSite site : locateProtocolCallSites.getOrDefault(project, List.of())) {
            if (!program.getName().equals(site.programName())) continue;
            Function func = program.getFunctionManager().getFunctionContaining(site.callSite());
            if (func != null) graph.tagLocator(func.getEntryPoint(), site.guidString());
        }
    }

    /**
     * Renders a CallGraph as a Graphviz dot string.
     * Node labels: "filename:function_name" with per-GUID installer/locator lines appended.
     * Node fill colour: plain=yellow, installer=green, locator=blue, both=orange.
     */
    private String generateCallGraphDot(String name, CallGraph graph) {
        String fileName = stripExtension(name);

        StringBuilder sb = new StringBuilder();
        sb.append("digraph \"").append(escapeLabel(name)).append("_calls\" {\n");
        sb.append("    rankdir=LR;\n");
        sb.append("    node [shape=box, fontname=\"Helvetica\", fontsize=10, style=filled];\n\n");

        for (CallGraph.Node n : graph.getNodes()) {
            boolean isInstaller = graph.getInstallerNodeIds().contains(n.id());
            boolean isLocator   = graph.getLocatorNodeIds().contains(n.id());
            String label = buildNodeLabel(fileName, n.name(),
                graph.getInstallerGuids(n.id()), graph.getLocatorGuids(n.id()));
            sb.append("    ").append(n.id())
              .append(" [label=\"").append(escapeLabel(label)).append("\"")
              .append(", fillcolor=\"").append(nodeColor(isInstaller, isLocator)).append("\"];\n");
        }

        sb.append("\n");
        for (CallGraph.Edge e : graph.getEdges()) {
            sb.append("    ").append(e.fromId()).append(" -> ").append(e.toId()).append(";\n");
        }

        sb.append("}\n");
        return sb.toString();
    }

    private static String buildNodeLabel(String fileName, String funcName,
            Set<String> instGuids, Set<String> locGuids) {
        StringBuilder sb = new StringBuilder(fileName).append(":").append(funcName);
        for (String g : instGuids) sb.append("\n[installer:").append(g).append("]");
        for (String g : locGuids)  sb.append("\n[locator:").append(g).append("]");
        return sb.toString();
    }

    private static String nodeColor(boolean isInstaller, boolean isLocator) {
        if (isInstaller && isLocator) return "#F0B27A";
        if (isInstaller)              return "#ABEBC6";
        if (isLocator)                return "#85C1E9";
        return "#F9E79F";
    }

    private void createExportSuperCallGraphAction() {
        exportSuperCallGraphAction = new DockingAction("Export Super Call Graph", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                Map<String, CallGraph> programGraphs = callGraphs.get(project);
                if (programGraphs == null || programGraphs.isEmpty()) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'Build Call Graph from Entry Point' for at least one program first.");
                    return;
                }

                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle("Save Super Call Graph");
                chooser.setSelectedFile(new File(project.getName() + "_super_callgraph.dot"));
                if (chooser.showSaveDialog(null) != JFileChooser.APPROVE_OPTION) return;

                File file = chooser.getSelectedFile();
                try (PrintWriter pw = new PrintWriter(file)) {
                    pw.print(generateSuperCallGraphDot(project.getName(), programGraphs));
                    ConsoleService console = tool.getService(ConsoleService.class);
                    if (console != null) {
                        console.println("[+] Super call graph written to: " + file.getAbsolutePath());
                    }
                } catch (IOException e) {
                    Msg.showError(this, null, "Export Failed", "Could not write file: " + e.getMessage());
                }
            }
        };
        exportSuperCallGraphAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Export Super Call Graph..." }, null, "Search"
        ));
        tool.addAction(exportSuperCallGraphAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Export Super Call Graph...'");
    }

    /**
     * Combines all per-program call graphs into a single dot graph.
     * A virtual "entry" diamond node has an edge to each program's entry point(s).
     * Node IDs are prefixed per program to avoid collisions. Color coding mirrors
     * generateCallGraphDot: installer=green, locator=blue, both=orange, plain=yellow.
     */
    private String generateSuperCallGraphDot(String projectName, Map<String, CallGraph> programGraphs) {
        StringBuilder sb = new StringBuilder();
        sb.append("digraph \"").append(escapeLabel(projectName)).append("_super\" {\n");
        sb.append("    rankdir=LR;\n");
        sb.append("    node [shape=box, fontname=\"Helvetica\", fontsize=10, style=filled];\n\n");

        sb.append("    entry [shape=diamond, fillcolor=\"#D7BDE2\", label=\"entry\"];\n\n");

        int progIndex = 0;
        for (Map.Entry<String, CallGraph> entry : programGraphs.entrySet()) {
            CallGraph cg = entry.getValue();
            String prefix   = "p" + progIndex + "_";
            String fileName = stripExtension(entry.getKey());

            for (CallGraph.Node n : cg.getNodes()) {
                boolean isInstaller = cg.getInstallerNodeIds().contains(n.id());
                boolean isLocator   = cg.getLocatorNodeIds().contains(n.id());
                String label = buildNodeLabel(fileName, n.name(),
                    cg.getInstallerGuids(n.id()), cg.getLocatorGuids(n.id()));
                sb.append("    ").append(prefix).append(n.id())
                  .append(" [label=\"").append(escapeLabel(label)).append("\"")
                  .append(", fillcolor=\"").append(nodeColor(isInstaller, isLocator)).append("\"];\n");
            }

            for (CallGraph.Edge e : cg.getEdges()) {
                sb.append("    ").append(prefix).append(e.fromId())
                  .append(" -> ").append(prefix).append(e.toId()).append(";\n");
            }

            for (String epId : cg.getEntryPointIds()) {
                sb.append("    entry -> ").append(prefix).append(epId).append(";\n");
            }

            progIndex++;
            sb.append("\n");
        }

        sb.append("}\n");
        return sb.toString();
    }

    private void createRunSliceAction() {
        runSliceAction = new DockingAction("Run Dataflow Slice", getName()) {
            @Override
            public void actionPerformed(ActionContext context) {
                Project project = tool.getProject();
                if (project == null) {
                    Msg.showInfo(getClass(), null, "No Project", "Please open a project first.");
                    return;
                }
                boolean hasData = !installProtocolCallSites.getOrDefault(project, List.of()).isEmpty()
                               || !locateProtocolCallSites.getOrDefault(project, List.of()).isEmpty();
                if (!hasData) {
                    Msg.showInfo(getClass(), null, "No Data",
                        "Run 'List LocateProtocol Callers' and 'List InstallProtocol Callers' first.");
                    return;
                }
                InputDialog dialog = new InputDialog("Dataflow Slice", "Enter the DXE module name (slicing criteria):");
                tool.showDialog(dialog);
                if (dialog.isCanceled()) return;
                String criteria = dialog.getValue();
                if (criteria == null || criteria.trim().isEmpty()) {
                    Msg.showInfo(getClass(), null, "Invalid Input", "Please provide a module name.");
                    return;
                }
                Map<String, String> results = runDependencySlice(project, criteria.trim());
                sliceResults.put(project, results);
            }
        };
        runSliceAction.setMenuBarData(new MenuData(
            new String[] { "Search", "Run Dataflow Slice..." }, null, "Search"
        ));
        tool.addAction(runSliceAction);
        log("[*] EFI Protocol Analyzer: registered menu item 'Search > Run Dataflow Slice...'");
    }

    /**
     * Backward dependency slice rooted at the module matching criteria.
     *
     * State per module: "remove" (default) or "keep".
     * Seed: GUIDs located by the slicing module → located set.
     * Fixpoint rule: if module M installs any GUID in located, mark M "keep" and
     *   add M's own located GUIDs to located (so M's dependencies propagate too).
     * Terminates because status is monotone (remove→keep only) and located only grows.
     */
    private Map<String, String> runDependencySlice(Project project, String criteria) {
        ConsoleService console = tool.getService(ConsoleService.class);

        // Build per-program install/locate GUID sets from collected call sites
        Map<String, Set<String>> programInstalls = new LinkedHashMap<>();
        Map<String, Set<String>> programLocates  = new LinkedHashMap<>();
        for (ProtocolCallSite site : installProtocolCallSites.getOrDefault(project, List.of())) {
            if (site.guidString() != null)
                programInstalls.computeIfAbsent(site.programName(), k -> new LinkedHashSet<>())
                               .add(site.guidString());
        }
        for (ProtocolCallSite site : locateProtocolCallSites.getOrDefault(project, List.of())) {
            if (site.guidString() != null)
                programLocates.computeIfAbsent(site.programName(), k -> new LinkedHashSet<>())
                              .add(site.guidString());
        }

        Set<String> allPrograms = new LinkedHashSet<>();
        allPrograms.addAll(programInstalls.keySet());
        allPrograms.addAll(programLocates.keySet());

        // Match slicing criteria against stripped program name (case-insensitive)
        String slicingProgram = null;
        for (String prog : allPrograms) {
            if (stripExtension(prog).equalsIgnoreCase(criteria) || prog.equalsIgnoreCase(criteria)) {
                slicingProgram = prog;
                break;
            }
        }
        if (slicingProgram == null) {
            if (console != null) console.println("[-] Slicing criteria not found: " + criteria);
            return new LinkedHashMap<>();
        }

        // All modules start as "remove"; slicing module is "keep"
        Map<String, String> status = new LinkedHashMap<>();
        for (String prog : allPrograms) status.put(prog, "remove");
        status.put(slicingProgram, "keep");

        // Seed located set from the slicing module
        Set<String> located = new LinkedHashSet<>(programLocates.getOrDefault(slicingProgram, Set.of()));

        // Fixpoint: propagate "keep" through install→locate chains
        boolean changed = true;
        while (changed) {
            changed = false;
            for (String prog : allPrograms) {
                if ("keep".equals(status.get(prog))) continue;
                for (String guid : programInstalls.getOrDefault(prog, Set.of())) {
                    if (located.contains(guid)) {
                        status.put(prog, "keep");
                        located.addAll(programLocates.getOrDefault(prog, Set.of()));
                        changed = true;
                        break;
                    }
                }
            }
        }

        // Report
        if (console != null) {
            console.println("\n[*] Dataflow slice — criteria: " + criteria);
            console.println("[+] Slicing module: " + stripExtension(slicingProgram));
            console.println("[+] Located GUIDs (seed + transitive, " + located.size() + "):");
            for (String g : located) console.println("      " + g);

            List<String> kept    = new ArrayList<>();
            List<String> removed = new ArrayList<>();
            for (String prog : allPrograms) {
                if (prog.equals(slicingProgram)) continue;
                if ("keep".equals(status.get(prog))) kept.add(prog);
                else removed.add(prog);
            }

            console.println("[+] Required modules (" + kept.size() + "):");
            for (String p : kept)    console.println("      " + stripExtension(p));
            console.println("[-] Removable modules (" + removed.size() + "):");
            for (String p : removed) console.println("      " + stripExtension(p));
        }

        return status;
    }

    @Override
    protected void dispose() {
        if (findCallsAction != null) {
            tool.removeAction(findCallsAction);
        }
        if (locateProtocolAction != null) {
            tool.removeAction(locateProtocolAction);
        }
        if (installProtocolAction != null) {
            tool.removeAction(installProtocolAction);
        }
        if (exportGraphAction != null) {
            tool.removeAction(exportGraphAction);
        }
        if (exportLocateCsvAction != null) {
            tool.removeAction(exportLocateCsvAction);
        }
        if (exportInstallCsvAction != null) {
            tool.removeAction(exportInstallCsvAction);
        }
        if (buildCallGraphAction != null) {
            tool.removeAction(buildCallGraphAction);
        }
        if (exportCallGraphAction != null) {
            tool.removeAction(exportCallGraphAction);
        }
        if (exportSuperCallGraphAction != null) {
            tool.removeAction(exportSuperCallGraphAction);
        }
        if (runSliceAction != null) {
            tool.removeAction(runSliceAction);
        }
        super.dispose();
    }
}
