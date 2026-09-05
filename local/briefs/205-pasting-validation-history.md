# PR 205: historical pasting validation records

Archived from the mathematical note during review repair F2. These are
superseded reports, not the current proof status or new validation claims.
The one-sided pasting theorem is now proved; the final assembly report below
supersedes the intermediate proof-hole reports. Original TeX is retained.

```tex
The preceding recheck was designated mathematical-gap session three,
conservatively charged as slot four of ten. The original start remains September~4, 2026, 23:45 UTC;
prior charged worker time is about 4 hours 31 minutes, including the partial
prover attempt. Operator investigation time is not known here and must also
be charged. This recheck does not reset the ten-session or approximately
one-and-a-half-working-day limit. The operator brief is retained unchanged.
At the end of that recheck, the mathematical argument and scalar estimate
were progress, not a fully formalized correction. The preceding continuation
was the fourth designated mathematical-gap
session, conservatively slot five of ten, started at September~5, 2026,
17:21:55 UTC. Its operator-supplied absolute deadline remains September~6,
2026, 11:45 UTC. The preceding handoff recorded about 5 hours 8 minutes of
worker time; this continuation must be charged in addition, together with
operator investigation time. Neither limit is reset. The next mathematical
step at that handoff was the averaged mirror estimate and its integration
into the fine-commutator assembly, not another Schmidt construction or
source-domain search. Both tasks are completed in the present continuation.

The present continuation is conservative slot six of ten, started September~5,
2026, 18:18:22 UTC. The original start and September~6, 11:45 UTC deadline
are unchanged. Prior recorded worker time is approximately 5 hours 46 minutes;
operator investigation time remains additional and is not known here.
At the September~5, 18:38 UTC validation cutoff, this continuation has used
about 20 minutes, for approximately 6 hours 6 minutes of recorded worker
time before operator accounting. Neither the session count nor the absolute
deadline requires escalation at this cutoff.
The correction is ready for independent review, not self-reviewed or
operator-adopted. No change to the session limit is requested.

\subsection*{Validation record of the preceding recheck}

The three edited Lean files, \path{Games/Sandwich.lean},
\path{Games/Sandwich/Pasting/CodewordConsistency.lean}, and
\path{Games/Sandwich/Pasting/Assembly.lean} under \path{MIPStarRE/QPBT/},
type-check. There is exactly one direct proof hole, in the restored
\leanid{exists\_pasting\_error}, and no added axiom. The conditional
dependency through \leanid{consistencyDefect\_codeword\_cross\_le} and
\leanid{consistencyDefect\_pasted\_le\_sqrt} is explicitly marked as
unfaithful as a derivation of the printed theorem.

The complete affected import chain was recompiled in a private temporary
copy of the compiled library: \path{CodewordConsistency.lean},
\path{PinchedReduction.lean}, \path{CrossMove.lean}, \path{Assembly.lean},
\path{Sandwich.lean}, the \path{QPBT.lean} aggregate, and the
root import file. All seven checks passed; the only warning in
that run was the tracked proof hole. The declaration checker resolved all
1521 blueprint names against these fresh artifacts. Its initial invocation
against the unchanged branch cache missed the two newly named declarations;
that stale-artifact result is not a missing source declaration.

As a computational check, NumPy with seed 201 tested the Schmidt matrix
estimate on 360 samples in dimensions $1,2,4,8,16,32$, including zero Schmidt
coefficients, coefficients decreasing to $10^{-12}$, and complex Hermitian
operators. No violation beyond the $10^{-10}$ tolerance occurred. A separate
two-dimensional computation returned forward and pasted defects zero and
reverse defect one for the product-state example. These checks supplement,
and do not replace, the scalar proof and the mathematical argument.

The blueprint web build, blueprint LaTeX convention check, and paper-gap
style check pass. The note builds with LaTeX and BibTeX. The global
blueprint/source synchronization script is not green: it reports 231 issues
outside the changed pasting entries. Those findings are not repaired here.
No full \verb|lake build| was run; the affected import-chain checks above
are not described as a full build or as proof convergence. No shared cache,
paper mirror, game definition, or operator-owned runtime record was edited.

\subsection*{Validation of the Schmidt-mirror continuation}

The new module \path{Games/Sandwich/Pasting/SchmidtMirror.lean} under
\path{MIPStarRE/QPBT/} type-checks without warnings or proof holes. The
generalized codeword-consistency and cross-move files also type-check, and
their old signatures remain proved specializations. The existing scalar
lemma was moved into the new module without changing its name or statement.
All earlier source-realignment edits and the operator brief are preserved.

Fresh temporary artifacts were used to recompile all eight affected modules:
\path{SchmidtMirror.lean}, \path{CodewordConsistency.lean},
\path{PinchedReduction.lean}, \path{CrossMove.lean}, \path{Assembly.lean},
\path{Sandwich.lean}, the QPBT aggregate, and the project root. All passed.
The only proof-hole warning is the existing one-sided pasting obligation;
no new proof hole or axiom was introduced. All 1540 blueprint declarations
resolve against these fresh artifacts. The blueprint web build, LaTeX
convention check, paper-gap style check, and standalone note build pass.
There was no full build or competing cache writer.

Kernel dependency checks of \leanid{exists\_schmidt\_coordinates},
\leanid{schmidtMirror\_norm\_sq\_le},
\leanid{schmidtMirrorMeasurement\_isProjective}, and all three new
distinct-family inequalities report only propositional extensionality,
classical choice, and quotient soundness. None depends on a proof-hole
axiom. An explicit interface check also instantiates the norm theorem on
the empty index type and zero vector; the general theorem itself permits
all singular and zero-coefficient cases. Thus the bounded mirror
construction task is complete, while the source pasting theorem remains
unfinished at that handoff pending the averaged estimate and fine-commutator
assembly. The next validation record supersedes that proof status.

\subsection*{Validation of the one-sided assembly}

In conservative session slot six, focused Lean checks succeed in dependency
order for the following eight modules, using a temporary copy of the compiled
library and writing fresh artifacts only under \path{/tmp/pasting-201-check}:
\begin{itemize}
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich/Pasting/SchmidtMirror.lean};
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich/Pasting/CodewordConsistency.lean};
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich/Pasting/PinchedReduction.lean};
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich/Pasting/CrossMove.lean};
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich/Pasting/Assembly.lean};
 \item \doclink{MIPStarRE/QPBT/Games/Sandwich.lean};
 \item the QPBT re-export and project root import files.
\end{itemize}
The last two import checks are not a full rebuild of all project proofs.
The eight modules form the complete actual import-consumer closure of the
changed pasting implementation in this checkout. The intended combining
consumers identified above have no call to the pasting theorem yet and retain
their independent proof holes.

The focused checks produce no proof-hole warning. The subsequent
\verb|sorry|/\verb|axiom| scan finds no occurrence in any of the five
modified or new Lean implementation files. Kernel dependency checks for
\leanid{exists\_pasting\_error},
\leanid{consistencyDefect\_schmidtMirror\_le},
\leanid{commutator\_mass\_fine\_le\_distinct\_families}, and
\leanid{consistencyDefect\_pasted\_le\_sqrt\_one\_sided} report only
\leanid{propext}, \leanid{Classical.choice}, and \leanid{Quot.sound};
in particular, the source theorem has no \leanid{sorryAx} dependency.

The blueprint web build succeeds, and the declaration checker against the
fresh temporary artifacts resolves all 1,544 linked declarations. The
paper-gap prose checker and blueprint LaTeX convention checker pass.
Two PDF compilation passes produce a 17-page note without unresolved
references or overfull boxes; the whitespace check also passes.
The global blueprint synchronization checker still reports 231 pre-existing
findings, the same count as in slot five; none concerns the changed pasting
entries. No guard is weakened, and no unrelated finding is repaired.
No full build, shared-cache write, push, merge, or independent review is
performed in this session. The operator brief is retained unchanged.

This continuation edits the sandwich root module, its codeword-consistency
and assembly modules, the Chapter 12 blueprint, and this note. The earlier
Schmidt-mirror module and cross-move edits are preserved. The theorem is
proved and ready for independent review; operator adoption and the unrelated
combining and extraction obligations remain outside this result.

```
