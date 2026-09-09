# Subagent token usage (generated 2026-09-05T18:29Z)

Codex totals count input + output tokens (cached input shown separately); Claude totals are the harness-reported subagent totals.

| pool:model | role | sessions | total tokens | input | cached input | output | reasoning | tool uses | wall hours |
|---|---|---|---|---|---|---|---|---|---|
| claude:claude-fable-5-1 | math-fix | 2 | 832,953 | 0 | 0 | 0 | 0 | 133 | 2.1 |
| claude:claude-fable-5-1 | mathfix | 3 | 1,344,540 | 0 | 0 | 0 | 0 | 101 | 2.6 |
| claude:claude-fable-5-1 | prover | 37 | 6,959,343 | 0 | 0 | 0 | 0 | 325 | 15.5 |
| claude:claude-fable-5-1 | repair | 2 | 758,703 | 0 | 0 | 0 | 0 | 125 | 1.5 |
| claude:claude-opus-5 | audit | 1 | 115,593 | 0 | 0 | 0 | 0 | 40 | 0.2 |
| claude:claude-opus-5 | cleanup | 1 | 155,865 | 0 | 0 | 0 | 0 | 65 | 0.5 |
| claude:claude-opus-5 | orc | 1 | 157,204 | 0 | 0 | 0 | 0 | 72 | 0.7 |
| claude:claude-opus-5 | prereview | 6 | 1,195,728 | 0 | 0 | 0 | 0 | 376 | 2.6 |
| claude:claude-opus-5 | prover | 64 | 14,437,550 | 0 | 0 | 0 | 0 | 2986 | 43.3 |
| claude:claude-opus-5 | refactor | 2 | 249,514 | 0 | 0 | 0 | 0 | 78 | 0.4 |
| claude:claude-opus-5 | repair | 58 | 8,114,183 | 0 | 0 | 0 | 0 | 2652 | 18.8 |
| claude:claude-opus-5 | review-fix | 19 | 3,258,862 | 0 | 0 | 0 | 0 | 1020 | 8.6 |
| claude:claude-opus-5 | reviewer | 33 | 5,813,897 | 0 | 0 | 0 | 0 | 1255 | 12.6 |
| claude:claude-opus-5 | reviewer-shadow | 1 | 185,012 | 0 | 0 | 0 | 0 | 42 | 0.3 |
| claude:claude-opus-5 | study | 1 | 83,405 | 0 | 0 | 0 | 0 | 24 | 0.1 |
| claude:claude-opus-5 | tooling | 1 | 99,804 | 0 | 0 | 0 | 0 | 39 | 0.3 |
| claude:claude-opus-5 (workflow) | reviewer | 3 | 3,945,000 | 0 | 0 | 0 | 0 | 785 | 2.1 |
| codex:dengnifer@local | orc | 1 | 71,950,470 | 71,723,864 | 70,171,392 | 226,606 | 100,596 | 0 | 3.3 |
| codex:dengnifer@local | reviewer | 22 | 118,935,017 | 118,354,013 | 110,395,648 | 581,004 | 300,892 | 0 | 7.3 |
| codex:drx@local | blueprint | 1 | 9,733,282 | 9,686,517 | 9,218,432 | 46,765 | 16,473 | 0 | 0.3 |
| codex:drx@local | mathfix | 1 | 16,089,488 | 16,008,169 | 15,771,520 | 81,319 | 35,174 | 0 | 0.6 |
| codex:drx@local | orc | 16 | 190,448,975 | 189,692,918 | 185,381,504 | 756,057 | 273,982 | 0 | 9.4 |
| codex:drx@local | prover | 16 | 86,585,266 | 86,234,168 | 83,822,336 | 351,098 | 145,878 | 0 | 4.1 |
| codex:drx@local | reviewer | 89 | 393,866,442 | 391,701,017 | 367,917,440 | 2,165,425 | 1,309,223 | 0 | 28.3 |
| codex:drx@local | scout | 14 | 34,182,576 | 33,949,874 | 31,344,640 | 232,702 | 115,197 | 0 | 2.1 |
| codex:drx@local | splitter | 2 | 20,894,445 | 20,772,238 | 20,171,776 | 122,207 | 57,966 | 0 | 1.1 |
| codex:main-issue0007 | orc | 1 | 4,422,393 | 4,393,275 | 4,192,512 | 29,118 | 15,345 | 0 | 0.4 |
| codex:main-mode1-20260905 | mathfix | 1 | 5,637,962 | 5,599,204 | 5,464,832 | 38,758 | 14,741 | 0 | 0.6 |
| codex:main-mode1-20260905 | prover | 9 | 12,339,386 | 12,295,243 | 11,853,184 | 44,143 | 6,042 | 0 | 1.0 |
| codex:main-mode1-20260905 | reviewer | 19 | 14,057,234 | 14,006,032 | 12,444,288 | 51,202 | 11,003 | 0 | 1.2 |
| codex:main-mode1-20260905 | scout | 1 | 947,423 | 939,439 | 859,136 | 7,984 | 1,751 | 0 | 0.2 |
| codex:orc-18-20260902-01 | prover | 1 | 10,418,399 | 10,383,923 | 10,121,728 | 34,476 | 11,895 | 0 | 0.4 |
| codex:orc-18-20260902-01 | splitter | 1 | 2,520,117 | 2,500,841 | 2,278,272 | 19,276 | 8,120 | 0 | 0.2 |
| codex:orc-38-20260903-01 | scout | 4 | 151,172 | 151,136 | 61,952 | 36 | 0 | 0 | 0.0 |
| codex:orc-67-20260904-01 | scout | 1 | 3,405,331 | 3,370,542 | 3,220,608 | 34,789 | 21,767 | 0 | 0.4 |
| codex:owner-operator | blueprint | 1 | 29,345,695 | 29,214,479 | 28,197,632 | 131,216 | 43,486 | 0 | 0.5 |
| codex:owner-operator | orc | 31 | 548,149,515 | 545,206,278 | 529,346,688 | 2,943,237 | 1,422,535 | 0 | 10.0 |
| codex:owner-operator | prover | 127 | 3,242,083,494 | 3,230,576,175 | 3,144,444,672 | 11,507,319 | 5,138,264 | 0 | 60.5 |
| codex:owner-operator | reviewer | 266 | 1,314,670,452 | 1,306,238,178 | 1,231,405,184 | 8,432,274 | 5,310,722 | 0 | 69.4 |

Grand totals: claude: 47,707,156, codex: 6,130,834,534

Claude records still marked running (no end record yet): 1
