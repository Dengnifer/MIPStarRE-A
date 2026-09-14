PR #483 publication is recovered at `6312792b97915eefdb60ef6bd18fcf62c8c21a0f`. GitHub and the remote branch match this clean local head.

The merge preserved `993c3611` and current main `8d33601f`; merge-loss guards passed, with only the required import union resolved. Exact-head CI is green with all nine `local-ci/*` statuses successful. No failed/needs-attention marker existed, so none was deleted.

Remaining handoff:
- Independent review is required; none was launched here.
- GitHub currently reports `mergeable_state: dirty` because the stacked base branch advanced to `8a46bbf7`; main should reassess after review.
- CI retained two advisory audit warnings in the [manifest](/home/drx/.cache/mipstarre-dev/ci-manifests/pr483-6312792b97915eefdb60ef6bd18fcf62c8c21a0f.json).