# Target journal: Proceedings of the American Mathematical Society

| Item | Details |
|---|---|
| Journal | Proceedings of the American Mathematical Society (PAMS) |
| Publisher | American Mathematical Society, Providence, Rhode Island |
| ISSN | 0002-9939 (print), 1088-6826 (electronic) |
| Homepage | https://www.ams.org/proc |
| Submission | https://ams.org/procsubmit: upload a PDF through the AMS Initial Manuscript Submission form (Centralized Manuscript Processing); questions to jrnl-initsub@ams.org |
| Review | double anonymous: submit `dist/LiuFanoIndexConjecture_final2-anonymous.pdf`, which has no author block and no repository link |
| Class file | `amsart` (AMS-LaTeX article class); the author package of each AMS journal is linked from https://www.ams.org/arc/journals/journal-select.html; the paper uses plain `amsart` |

## Scope fit

PAMS publishes shorter research articles, not exceeding 15 printed pages, in
all areas of pure and applied mathematics. The paper is a short counterexample
in birational geometry: it settles in the negative, in dimension four,
Conjecture 4.2 of H. Liu, *On Fano indices of weighted projective spaces*,
arXiv:2608.03434v3 (2026), which states that the Fano indices of canonical
weighted projective n-spaces (with 1, ..., n), the indices of terminal
Calabi-Yau n-folds and the indices of n-dimensional log canonical
singularities form the same set. Related work on the indices of Calabi-Yau
varieties, used in the paper: L. Esser, B. Totaro, C. Wang, *Calabi-Yau
varieties of large index*, arXiv:2209.04597.

MSC 2020: primary 14J32; secondary 14B05, 14J45, 14M25.

## Length and format

- 8 pages in `amsart` (7 in the anonymized version), well under the limit of
  15 printed pages, with three schematic figures; built with no overfull or
  underfull boxes.
- One-sentence abstract; MSC codes, keywords and the corresponding author in
  the first-page footnotes, as `amsart` places them.
- Two authors: Deep Bhattacharjee (corresponding author) and Ushashi
  Bhattacharya, with addresses, e-mail addresses and ORCID iDs.
- The source is a single file `main.tex` with the references in the source
  (`thebibliography`), so no `.bib` or `.bbl` file is needed.
  `dist/LiuFanoIndexConjecture_final2-tex.zip` and the arXiv tarball contain
  this file and the figures as PNG.
- `pdflatex "\def\anonymous{}\input{main}"` gives the anonymized version
  (`scripts/build_paper.sh` builds both). The anonymized version keeps the
  statement on the use of AI tools and replaces the repository link by
  "supplied with the submission"; upload the master zip, or the repository
  without its author files, as supplementary material if the form asks for
  the code.
- Declarations at the end: "Acknowledgements" (use of AI), "Competing
  interests: None", "Funding: None" and "Data availability" (who computed
  what, the Zenodo DOI of the Lean formalization and the link to the PDF in
  `preprintLiuFanoIndexConjecture/`).
- The pages of the AMS site (ams.org) returned HTTP 403 to the session that
  prepared this file, so the details above come from search results quoting
  those pages; read the submission page once more before submitting.

## Policy on AI assistance

- The AMS Committee on Publications has adopted the statement of the
  Committee on Publication Ethics (COPE) on AI in authoring ("Ethical
  Guidelines and AMS Journal Policies", https://www.ams.org/publications/journals/policies/policies,
  section "Use of Artificial Intelligence in Authoring"; see also Notices of
  the AMS, January 2024). Under that statement AI tools cannot be authors,
  since they cannot take responsibility for the work, and authors who use AI
  tools in writing the manuscript or in collecting and analysing data must
  disclose, in the methods or a similar section, which tool was used and how;
  the authors remain fully responsible for the content.
- The paper's "Acknowledgements" name Claude Code (Anthropic) and say how
  it was used; "Data availability" repeats it. Add the version of the tool in the
  submitted manuscript if the editors ask for it.
- Every computational step of the non-membership 1389 notin I_{4,wps} is
  checked by the Lean 4 kernel (Section 6 of the paper); the geometric steps
  rest on the cited literature and are proved by hand in the paper.
