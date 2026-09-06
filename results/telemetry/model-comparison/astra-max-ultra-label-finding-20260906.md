# Astra API max and official Ultra: evidence boundaries

Recorded using ghz UTC 2026-09-06T03:42:05Z. The owner asks whether sub2api max is the same as Ultra in an official subscription. This is a research finding, not a new effort or delegation policy.

The official Astra API documents max as its highest listed reasoning.effort value, alongside xhigh; ultra is not listed. Thus max is an official API value, not merely a private name invented by the relay. [Astra API](https://developers.openai.com/api/docs/models/gpt-6-astra).

Official product documentation distinguishes Max, which allocates more reasoning to a single task, from Ultra, which combines maximum reasoning with proactive subagent delegation. It also says Max may need enabling in app settings. A picker omitting Max does not by itself prove a different backend tier. [Models](https://learn.chatgpt.com/docs/models#know-when-to-use-max-or-ultra), [Subagents](https://learn.chatgpt.com/docs/agent-configuration/subagents#choosing-models-and-reasoning).

Inference: relay max is consistent with the maximum-reasoning component of official Ultra. The documents and available measurements do not establish full-mode equivalence or the deployed sub2api server's exact upstream mapping.

The earlier saved probes requested literal max, ultra and xhigh through a fresh raw Codex CLI on both endpoints. Completion metadata reported max, medium and xhigh respectively. They did not capture the outgoing wire body, locate the transformation, measure backend compute or compare task quality. In particular, literal ultra returning medium is not a test of the official subscription's Ultra picker mode. The probes and project workers explicitly disabled automatic fan-out.

For project research, label the current comparison Astra API max versus xhigh with automatic fan-out off. Keep UI mode, configured API effort, server-reported effort and delegation behavior as separate fields. Do not rename the relay max group Ultra or infer a reasoning-budget equivalence that was not measured. This leaves the owner's max/xhigh task-dependent policy unchanged.

A bounded read-only helper independently checked this inference against the saved probe report and the fetched official-documentation facts. It performed no ghz access, model probes, policy changes or project assignments. Main owns incorporating the finding into project comparison records; repository publication is pending verification.
