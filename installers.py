import csv
import os
import re
import sys


# Match InstallProtocolInterface or InstallMultipleProtocolInterfaces calls,
# then capture every &SomethingGuid argument that follows up to the closing paren.
CALL_PATTERN = re.compile(
    r"Install(?:Multiple)?ProtocolInterfaces?\s*\((?P<args>[^;]*?)\)\s*;",
    re.DOTALL,
)
GUID_PATTERN = re.compile(r"&\s*([A-Za-z_][A-Za-z0-9_]*Guid)\b")

# Extract the Dxe module name from a path like ".../PL061GpioDxe/PL061Gpio.c"
DXE_DIR_PATTERN = re.compile(r"([A-Za-z0-9_]+Dxe)")


def find_dxe_module(filepath):
    """Walk up the path components and return the first one ending in 'Dxe'."""
    parts = os.path.normpath(filepath).split(os.sep)
    for part in reversed(parts):
        if DXE_DIR_PATTERN.fullmatch(part):
            return part
    return None


def extract_calls(source):
    """Yield (guid,) for each guid installed via (Multiple)ProtocolInterface(s)."""
    for call in CALL_PATTERN.finditer(source):
        args = call.group("args")
        for guid_match in GUID_PATTERN.finditer(args):
            yield guid_match.group(1)


def process_directory(root_dir, writer):
    for dirpath, _dirnames, filenames in os.walk(root_dir):
        for name in filenames:
            if not name.endswith((".c", ".h")):
                continue
            filepath = os.path.join(dirpath, name)
            module = find_dxe_module(filepath)
            if not module:
                continue
            try:
                with open(filepath, "r", encoding="utf-8", errors="replace") as f:
                    source = f.read()
            except OSError:
                continue
            for guid in extract_calls(source):
                writer.writerow([module, guid])


def main():
    if len(sys.argv) < 2:
        print("Usage: python find_protocols.py <directory> [output.csv]", file=sys.stderr)
        sys.exit(1)

    root_dir = sys.argv[1]
    out_path = sys.argv[2] if len(sys.argv) >= 3 else "-"

    if out_path == "-":
        writer = csv.writer(sys.stdout)
        writer.writerow(["DxeModule", "Guid"])
        process_directory(root_dir, writer)
    else:
        with open(out_path, "w", newline="", encoding="utf-8") as out:
            writer = csv.writer(out)
            writer.writerow(["DxeModule", "Guid"])
            process_directory(root_dir, writer)


if __name__ == "__main__":
    main()
