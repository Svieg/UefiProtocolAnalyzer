#!/usr/bin/env python3
"""
efiseek_guid_lookup.py

Translate UEFI GUIDs to their symbolic names using the efiSeek Ghidra
plugin's GUID database (data/guids-db.ini).

The efiSeek database stores entries one-per-line in the form:
    NAME = {xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx}

This script can:
  * Look up one or more GUIDs from the command line.
  * Translate every GUID it finds inside an arbitrary text/log/binary file.
  * Be imported as a module (use `GuidDatabase`).

Usage:
    # Look up specific GUIDs
    python efiseek_guid_lookup.py -d guids-db.ini ef9fc172-a1b2-4693-b327-6d32fc416042

    # Translate every GUID found inside a file
    python efiseek_guid_lookup.py -d guids-db.ini --scan some_dump.txt

    # Read GUIDs from stdin (one per line)
    cat guids.txt | python efiseek_guid_lookup.py -d guids-db.ini -

    # Auto-download the database from the upstream repo on first use
    python efiseek_guid_lookup.py --fetch ef9fc172-a1b2-4693-b327-6d32fc416042
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, Iterable, Iterator, Optional, Tuple

# Default upstream location for the efiSeek GUID database.
EFISEEK_DB_URL = (
    "https://raw.githubusercontent.com/DSecurity/efiSeek/master/data/guids-db.ini"
)

# Matches a standard 8-4-4-4-12 hex GUID, with or without surrounding braces.
GUID_RE = re.compile(
    r"\{?([0-9a-fA-F]{8})-"
    r"([0-9a-fA-F]{4})-"
    r"([0-9a-fA-F]{4})-"
    r"([0-9a-fA-F]{4})-"
    r"([0-9a-fA-F]{12})\}?"
)

# Matches a single "NAME = {guid}" line from guids-db.ini.
DB_LINE_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*"
    r"\{([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-"
    r"[0-9a-fA-F]{4}-[0-9a-fA-F]{12})\}\s*$"
)


def normalize_guid(guid: str) -> Optional[str]:
    """Return a canonical lowercase 8-4-4-4-12 representation, or None."""
    m = GUID_RE.search(guid)
    if not m:
        return None
    return "-".join(p.lower() for p in m.groups())


class GuidDatabase:
    """In-memory mapping of canonical-lowercase GUID -> symbolic name."""

    def __init__(self, mapping: Optional[Dict[str, str]] = None) -> None:
        self._map: Dict[str, str] = dict(mapping or {})

    def __len__(self) -> int:
        return len(self._map)

    def __contains__(self, guid: str) -> bool:
        norm = normalize_guid(guid)
        return norm is not None and norm in self._map

    def lookup(self, guid: str) -> Optional[str]:
        norm = normalize_guid(guid)
        if norm is None:
            return None
        return self._map.get(norm)

    def items(self) -> Iterable[Tuple[str, str]]:
        return self._map.items()

    @classmethod
    def from_ini(cls, path: Path) -> "GuidDatabase":
        mapping: Dict[str, str] = {}
        with path.open("r", encoding="utf-8", errors="replace") as fh:
            for lineno, raw in enumerate(fh, 1):
                line = raw.strip()
                # Skip blank lines, INI section headers, comments.
                if not line or line.startswith((";", "#", "[")):
                    continue
                m = DB_LINE_RE.match(line)
                if not m:
                    # Silently skip malformed lines; they shouldn't be present
                    # in the upstream file but we want to be tolerant.
                    continue
                name, guid = m.group(1), m.group(2).lower()
                # Keep the first definition if duplicates ever appear.
                mapping.setdefault(guid, name)
        return cls(mapping)

    @classmethod
    def from_url(cls, url: str = EFISEEK_DB_URL) -> "GuidDatabase":
        # Imported lazily so the script works without a network when --fetch
        # isn't requested.
        from urllib.request import urlopen

        with urlopen(url) as resp:  # noqa: S310 - intentional remote fetch
            data = resp.read().decode("utf-8", errors="replace")

        mapping: Dict[str, str] = {}
        for line in data.splitlines():
            line = line.strip()
            if not line or line.startswith((";", "#", "[")):
                continue
            m = DB_LINE_RE.match(line)
            if not m:
                continue
            name, guid = m.group(1), m.group(2).lower()
            mapping.setdefault(guid, name)
        return cls(mapping)


def iter_guids_in_text(text: str) -> Iterator[Tuple[int, int, str]]:
    """Yield (start, end, canonical_guid) for every GUID found in `text`."""
    for m in GUID_RE.finditer(text):
        canonical = "-".join(p.lower() for p in m.groups())
        yield m.start(), m.end(), canonical


def cmd_lookup(db: GuidDatabase, guids: Iterable[str]) -> int:
    missing = 0
    for raw in guids:
        norm = normalize_guid(raw)
        if norm is None:
            print(f"{raw}\t<invalid GUID>")
            missing += 1
            continue
        name = db.lookup(norm)
        if name is None:
            print(f"{norm}\t<unknown>")
            missing += 1
        else:
            print(f"{norm}\t{name}")
    return 0 if missing == 0 else 1


def cmd_scan(db: GuidDatabase, path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="replace")
    seen: Dict[str, str] = {}
    for _, _, guid in iter_guids_in_text(text):
        if guid in seen:
            continue
        seen[guid] = db.lookup(guid) or "<unknown>"
    for guid, name in seen.items():
        print(f"{guid}\t{name}")
    return 0


def parse_args(argv: Optional[Iterable[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Translate UEFI GUIDs using the efiSeek guids-db.ini database."
    )
    src = parser.add_mutually_exclusive_group()
    src.add_argument(
        "-d",
        "--db",
        type=Path,
        help="Path to a local copy of efiSeek's guids-db.ini.",
    )
    src.add_argument(
        "--fetch",
        action="store_true",
        help=f"Download the database from {EFISEEK_DB_URL} on the fly.",
    )
    parser.add_argument(
        "--scan",
        type=Path,
        metavar="FILE",
        help="Scan FILE for any GUIDs and print their names.",
    )
    parser.add_argument(
        "guids",
        nargs="*",
        help='GUIDs to look up. Use "-" to read GUIDs from stdin (one per line).',
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Optional[Iterable[str]] = None) -> int:
    args = parse_args(argv)

    if args.fetch:
        db = GuidDatabase.from_url()
    elif args.db:
        if not args.db.is_file():
            print(f"error: database not found: {args.db}", file=sys.stderr)
            return 2
        db = GuidDatabase.from_ini(args.db)
    else:
        print(
            "error: provide --db PATH or --fetch to load the GUID database.",
            file=sys.stderr,
        )
        return 2

    print(f"# loaded {len(db)} GUIDs", file=sys.stderr)

    if args.scan:
        return cmd_scan(db, args.scan)

    guids = list(args.guids)
    if not guids:
        print("error: no GUIDs given (and no --scan FILE).", file=sys.stderr)
        return 2

    if guids == ["-"]:
        guids = [ln.strip() for ln in sys.stdin if ln.strip()]

    return cmd_lookup(db, guids)


if __name__ == "__main__":
    sys.exit(main())
