#!/usr/bin/env python3
import json
import re
import subprocess
import sys
from pathlib import Path

BANNED = ("under construction", "not to be cited", "0.1.0-dev")

def main():
    if len(sys.argv) != 2:
        print("usage: check_release_metadata.py <TAG>")
        return 2
    tag = sys.argv[1]
    match = re.fullmatch(r"v?(\d+\.\d+\.\d+)(?:-.+)?", tag)
    if not match:
        print("INVALID_TAG_FORMAT")
        return 1
    expected = match.group(1)
    root = Path(__file__).resolve().parents[1]
    citation = (root / "CITATION.cff").read_text(encoding="utf-8")
    zenodo = json.loads((root / ".zenodo.json").read_text(encoding="utf-8"))
    origin = subprocess.check_output(["git", "-C", str(root), "config", "--get", "remote.origin.url"], text=True).strip()
    repo = re.sub(r"\.git$", "", origin).replace("git@github.com:", "https://github.com/")
    errors = []
    citation_version = re.search(r"^version:\s*([^\s#]+)", citation, re.MULTILINE)
    if not citation_version or citation_version.group(1).strip("\"'") != expected:
        errors.append("CITATION_VERSION")
    if str(zenodo.get("version", "")) != expected:
        errors.append("ZENODO_VERSION")
    identifiers = zenodo.get("related_identifiers", []) or []
    if not any(i.get("identifier") == repo for i in identifiers):
        errors.append("REPOSITORY_URL")
    if str(zenodo.get("license", "")) not in {"Apache-2.0", "apache2.0"}:
        errors.append("LICENSE")
    description = str(zenodo.get("description", "")).lower()
    if any(term in description for term in BANNED):
        errors.append("OBSOLETE_WORDING")
    if errors:
        print("RELEASE_METADATA_RESULT=FAIL")
        print("ERRORS=" + ",".join(errors))
        return 1
    print("RELEASE_METADATA_RESULT=PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
