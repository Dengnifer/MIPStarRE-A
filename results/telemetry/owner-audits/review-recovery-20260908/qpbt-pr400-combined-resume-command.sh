#!/usr/bin/env bash
# Primary publication coordinator: run only after issue475's reviewed repair merges.
# Preserve the original request's null activation boundary and complete author set.
exec env -u MIPSTARRE_MODEL_POLICY_ACTIVATION_AT \
  MIPSTARRE_CACHE_ROOT=/home/drx/.cache/mipstarre-dev \
  MIPSTARRE_NATIVE_REVIEW_ROOT=01a076bc-f4ad-7813-805b-c8b4dac71a14 \
  MIPSTARRE_NATIVE_REVIEW_AUTHORS=01a076bc-f4ad-7813-805b-c8b4dac71a14,01a08101-a7eb-7891-bd8e-2f96cc325389,01a08135-8ad7-7de1-808b-091ee156c60a \
  MIPSTARRE_REVIEW_JOB_CLASS=hard_review \
  MIPSTARRE_REVIEW_MODEL=gpt-6-astra \
  MIPSTARRE_PROSE_MODEL=gpt-6-astra \
  MIPSTARRE_REVIEW_EFFORT=ultra \
  MIPSTARRE_REVIEW_HARDNESS_REASON='Coupled Claim 17-1/17-3 review across current QPBT source-domain APIs, subline witness construction, placement identities, weighted positive-operator estimates, and the paper-facing Claim 17-3 bound.' \
  /home/drx/MIPStarRE-qpbt/local/bin/review.sh 400 \
  --resume-native-request /home/drx/.cache/mipstarre-dev/native-reviews/48c8adbc83d749b0b79fb9faac681534.json \
  --resume-native-prose-request /home/drx/.cache/mipstarre-dev/native-reviews/8aaa7139221c4975a2082d886b77714d.json
