# Post-deviations packaging integration check

Source snapshot:862f5f71e8042c7cab15918025c4f592f74c9ed0, after service merges
of packaging659 and deviations650. This is an intermediate no-PDF integration
check, not the final artifact or an official comparator result.

Both normal and anonymized make_artifact.sh runs exited0. Each contains874
files including MANIFEST,673 Lean files, and docs/DEVIATIONS.md. Each leak
scan found16 raw hits,16 allowed hits and0 remaining. The anonymized check
found no surviving configured identity string. Every MIPStarRE import resolves
inside each snapshot. The manifests accurately retain two absent legacy LDT
paper locators: references/ldt-paper/commutativity_points.tex and
references/ldt-paper/projectivization.tex. No PDF was built or scanned.

Normal archive SHA256:
b23b4a03f194abefdc33455b4eb1a797e19559d0993f0e9909898b43af32a00d.
Anonymized archive SHA256:
ddbd723e3274c6fcc4a4df78ca03f4fb246bd649ae29f7242d353a224b59456c.
Outputs and retained trees:
/tmp/main-cpa-artifact-post650-20260921-normal and
/tmp/main-cpa-artifact-post650-20260921-anon.
Log:/tmp/main-cpa-artifact-post650-20260921.log; exit receipt0.
Manifest timestamps are14:48:33 and14:48:40 UTC on2026-09-21.

Final updated documentation, terminal source-adoption classifications,
official four-target comparator acceptance and the final exact-commit checks
remain outstanding. The current two workers and PR663 CI were verified live;
no third model lane or native delegate was admitted.
