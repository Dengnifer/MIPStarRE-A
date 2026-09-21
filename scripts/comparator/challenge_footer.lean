
-- Template footer for the comparator challenge of this repository's default
-- track.  The generated challenge file ends with exactly this text, so it
-- carries the ONE intentional hole of the whole repository: the headline
-- theorem, stated here and proved in the library.  Two rules hold it together:
--
--   * the declaration must be `theorem mainFormal`, at column zero, and its
--     proof must be the two lines `:= by` / `sorry` — that is the shape
--     `scripts/generate_badges.py` recognises when it subtracts this one hole
--     from the repository's sorry count;
--   * the statement must be the headline theorem's statement, character for
--     character as the library declares it, inside the library's namespace.
--
-- Replace the placeholder below with this project's headline theorem when it
-- exists, keeping both rules.  Until then the challenge states `True`, which
-- is honest: nothing has been claimed yet.

namespace PaperLib
namespace Test

-- source: <the library file and line range that declares this theorem>
/--
Source statement of `<blueprint label>`.

Paper origin: `references/<mirror>-paper/<file>.tex:<lines>`.

Any difference between the paper's statement and this one belongs in a
paper-gap note under `docs/paper-gaps/` and must be cited here. -/
theorem mainFormal : True := by
  sorry

end Test
end PaperLib
