# Dispatch for Challenger 1 (Phase 5 Milestone 1 Iteration 2 Gate)

## Identity
- Type: teamwork_challenger
- Role: Milestone 1 Iteration 2 Adversarial Challenger 1
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_m1_iter2_1
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Objective
Adversarially challenge the remediation changes:
1. Try to bypass the 9B model policy with every variant of CLI flags and programmatic calls:
   - `python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "Test"`
   - `python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "Test"`
   - `python3 tools/ollama_lean4_client.py query --model llama3:70b --prompt "Test"`
   - Verify that 0 HTTP 404s occur in server logs and 12B/27B is never dispatched to Ollama `/api/generate`.
2. Inspect `data/gemma_accepted_proofs.jsonl`:
   - Assert `sorry` is completely absent: `python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl'))"`
   - Assert dummy proofs are completely absent: `python3 -c "import json; proofs = [json.loads(l) for l in open('data/gemma_accepted_proofs.jsonl')]; assert not any('exact ' in p.get('proof', '') and '-- Proved declaration in' in p.get('proof', '') for p in proofs)"`
   - Assert no spurious docstring words (`with`, `in`, `for`, etc.) exist as theorem names.
3. Stress test `tools/phase_axiom_census.sh` with invalid/empty prefixes:
   - `./tools/phase_axiom_census.sh ""` (must exit 1)
   - `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` (must exit 1)
   - `./tools/phase_axiom_census.sh CompletelyBogus` (must exit 1)

Provide explicit verdict: APPROVE or REJECT.
Write findings to `challenge.md` and `handoff.md` and message the orchestrator.

## Mandatory Inputs to Read
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- GATE_STATUS.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/GATE_STATUS.md`
- Worker Handoff: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter2/handoff.md`

## 2026-11-04T23:03:25Z
You are challenger_m1_iter2_1.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_m1_iter2_1
Read your task in: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_m1_iter2_1/DISPATCH.md
Read ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read Worker Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter2/handoff.md

Adversarially challenge the remediation changes:
- Try to bypass 9B policy with --model 12B/27B/70B (must redirect to 9B with warning, 0 404s).
- Verify data/gemma_accepted_proofs.jsonl has 0 sorry substrings, 0 dummy proofs, and 937 valid records.
- Verify census exits code 1 on non-existent prefix and empty string.
Write findings to `challenge.md` and `handoff.md` with explicit verdict APPROVE or REJECT, and message me.
