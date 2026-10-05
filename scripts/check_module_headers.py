#!/usr/bin/env python3
"""Check module headers, source sizes and symlinks before a Palomar upload.

The sources are the tracked files together with untracked files that git does not ignore, so
the check also covers new modules before they are committed.
"""

from pathlib import Path
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=root,
    ).decode("utf-8").split("\0")
    deleted = set(subprocess.check_output(
        ["git", "ls-files", "-z", "--deleted", "--", "*.lean"], cwd=root,
    ).decode("utf-8").split("\0"))
    sources = sorted({path for path in paths if path and path not in deleted})
    failures = []
    for source in sources:
        try:
            path = root / source
            if path.is_symlink():
                failures.append(f"{source}: submitted Lean sources must not be symlinks")
                continue
            content = path.read_bytes()
            text = content.decode("utf-8")
            line_count = content.count(b"\n") + int(bool(content) and not content.endswith(b"\n"))
            limit = 1000 if source == "Challenge.lean" else 10000
            if line_count > limit:
                failures.append(f"{source}: {line_count} lines exceeds the {limit}-line limit")
            if source == "Challenge.lean" and len(content) > 100 * 1024:
                failures.append(f"{source}: exceeds the 100 KiB challenge limit")
            lines = text.lstrip().splitlines()
            if path.name != "lakefile.lean" and (not lines or lines[0].strip() != "module"):
                failures.append(f"{source}: must begin with `module` on its own line")
        except (OSError, UnicodeError) as error:
            failures.append(f"{source}: {error}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    if not sources:
        print("No Lean sources found", file=sys.stderr)
        return 1
    print(f"Module headers, sizes and symlinks checked: {len(sources)} Lean sources")
    return 0


if __name__ == "__main__":
    sys.exit(main())
