"""Regression tests for source drift that previously passed the correspondence check."""

import copy
from pathlib import Path
import tempfile
import unittest

from check_paper_correspondence import (
    ManifestError, check_paper_coverage, prose_span, scan_paper_file,
    source_fingerprint, validate_manifest,
)


class CorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / "paper.tex"
        self.source = r"""
\begin{theorem}\label{thm:main} For $x>0$, $f(x)>0$.\end{theorem}
\begin{definition} A separated system has property P.\end{definition}
\begin{remark} The optional extension uses a Schwarzian.\end{remark}
Example starts here. The contraction bound is $1/5$. Example ends here.
"""
        self.path.write_text(self.source)
        self.entries = []
        for d, source, match in zip(scan_paper_file(self.path),
                ("thm:main", "unlabelled:separation", "unlabelled:extension"),
                (None, "A separated system", "The optional extension")):
            entry = dict(source=source, kind=d.kind, sha256=source_fingerprint(d.text),
                         status="intentionally_unformalized", reason="Test fixture.")
            if match:
                entry["match"] = match
            self.entries.append(entry)
        self.entries.append(dict(source="prose:example", kind="prose", file="paper.tex",
            start="Example starts here.", end="Example ends here.",
            sha256=source_fingerprint(prose_span(self.source, "Example starts here.", "Example ends here.")),
            status="intentionally_unformalized", reason="Test fixture."))
        self.snapshots = {"paper.tex": source_fingerprint(self.source)}

    def check_source(self, source, refresh_snapshot=False):
        self.path.write_text(source)
        snapshots = {"paper.tex": source_fingerprint(source)} if refresh_snapshot else self.snapshots
        return check_paper_coverage(self.root, ["paper.tex"], self.entries, snapshots)[0]

    def test_reviewed_source_passes(self):
        self.assertEqual(self.check_source(self.source), [])

    def test_layout_and_comments_pass(self):
        source = self.source.replace("For $x", "For\n  $x") + "% editorial note\n"
        self.assertEqual(self.check_source(source), [])

    def test_same_label_changed_statement_fails(self):
        errors = self.check_source(self.source.replace("f(x)>0", "f(x)<0"), True)
        self.assertTrue(any("thm:main: content changed" in e for e in errors))

    def test_same_count_replaced_unlabelled_statement_fails(self):
        errors = self.check_source(self.source.replace("property P", "property Q"), True)
        self.assertTrue(any("unlabelled:separation: content changed" in e for e in errors))

    def test_new_remark_requires_entry(self):
        errors = self.check_source(self.source + r"\begin{remark} New claim.\end{remark}", True)
        self.assertTrue(any("unlabelled remark missing" in e for e in errors))

    def test_prose_change_with_same_anchors_fails(self):
        errors = self.check_source(self.source.replace("1/5", "1/4"), True)
        self.assertTrue(any("prose:example: content changed" in e for e in errors))

    def test_new_unmapped_prose_requires_review(self):
        errors = self.check_source(self.source + "A new mathematical claim.\n")
        self.assertTrue(any("manuscript content changed" in e for e in errors))

    def test_ambiguous_unlabelled_match_fails(self):
        errors = self.check_source(self.source +
            r"\begin{definition} A separated system has property Q.\end{definition}", True)
        self.assertTrue(any("found 2" in e for e in errors))

    def test_exclusion_requires_reason(self):
        data = dict(manuscript_files=["paper.tex"], manuscript_sha256=self.snapshots,
                    entries=copy.deepcopy(self.entries))
        validate_manifest(data, self.path)
        del data["entries"][2]["reason"]
        with self.assertRaisesRegex(ManifestError, "needs a reason"):
            validate_manifest(data, self.path)


if __name__ == "__main__":
    unittest.main()
