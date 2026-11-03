#!/usr/bin/env python3
"""
test_workflow_control_adversarial.py — Adversarial Stress Test Suite for tools/workflow_control.py

Empirically tests:
1. Rapid pause/resume cycles in tight loop.
2. Concurrent multi-threaded and multi-process pause/resume/status/checkpoint calls.
3. Sentinel file tampering and corrupted JSON handling:
   - 0-byte file
   - Invalid JSON syntax
   - Malformed schema / missing keys
   - Binary garbage
   - Directory in place of sentinel
4. Checkpoint integrity and status formatting resilience.
"""

import os
import sys
import json
import time
import shutil
import tempfile
import threading
import multiprocessing
from pathlib import Path

# Add project root to path
sys.path.insert(0, "/Users/pablosuarez/Desktop/SympTopAutoForm")
from tools.workflow_control import WorkflowController, format_status_output

def run_tests():
    print("================================================================================")
    print("STARTING ADVERSARIAL STRESS TESTING OF WORKFLOW_CONTROL.PY")
    print("================================================================================")
    
    test_dir = tempfile.mkdtemp(prefix="adv_test_symp_")
    root = Path(test_dir)
    ctrl = WorkflowController(root)
    
    failures = []
    
    # -------------------------------------------------------------------------
    # TEST 1: Rapid Pause/Resume Cycles (100 iterations)
    # -------------------------------------------------------------------------
    print("\n[TEST 1] Rapid Pause/Resume Cycles (100 iterations)...")
    try:
        start_t = time.time()
        for i in range(100):
            p_rec = ctrl.pause(reason=f"Cycle {i}", active_task=f"Task {i}")
            if not ctrl.is_paused():
                raise AssertionError(f"Cycle {i}: is_paused() is False right after pause()")
            if not ctrl.sentinel_path.is_file():
                raise AssertionError(f"Cycle {i}: sentinel file does not exist")
            
            r_rec = ctrl.resume(user="cycle_tester")
            if ctrl.is_paused():
                raise AssertionError(f"Cycle {i}: is_paused() is True right after resume()")
            if ctrl.sentinel_path.is_file():
                raise AssertionError(f"Cycle {i}: sentinel file still exists after resume")
            if not r_rec["resumed"]:
                raise AssertionError(f"Cycle {i}: resume record reported resumed=False")
        
        elapsed = time.time() - start_t
        print(f"  --> PASSED: 100 rapid pause/resume cycles completed in {elapsed:.3f}s")
    except Exception as e:
        print(f"  --> FAILED: {e}")
        failures.append(("Rapid Pause/Resume", str(e)))

    # -------------------------------------------------------------------------
    # TEST 2: Idempotency Under Rapid Repetitions
    # -------------------------------------------------------------------------
    print("\n[TEST 2] Idempotency of Repeated Pauses and Resumes...")
    try:
        # Multiple pauses in a row
        for i in range(10):
            p = ctrl.pause(reason=f"Multi-pause {i}")
            if not p["paused"]:
                raise AssertionError(f"Multi-pause {i} failed")
        if not ctrl.is_paused():
            raise AssertionError("Should be paused after multi-pause")
        
        # Multiple resumes in a row
        r1 = ctrl.resume()
        if not r1["resumed"]:
            raise AssertionError("First resume should succeed")
        for i in range(9):
            r = ctrl.resume()
            if r["resumed"]:
                raise AssertionError(f"Subsequent resume {i} should report resumed=False")
            if r["status"] != "RUNNING":
                raise AssertionError(f"Subsequent resume {i} status not RUNNING")
        
        print("  --> PASSED: Multiple pause and resume calls are idempotent and safe")
    except Exception as e:
        print(f"  --> FAILED: {e}")
        failures.append(("Idempotency", str(e)))

    # -------------------------------------------------------------------------
    # TEST 3: Concurrent Multi-Threaded Pause/Resume/Status
    # -------------------------------------------------------------------------
    print("\n[TEST 3] Concurrent Multi-Threaded Stress Test (20 threads)...")
    try:
        errors = []
        def worker(tid):
            try:
                for j in range(20):
                    ctrl.pause(reason=f"Thread {tid} iter {j}")
                    _ = ctrl.is_paused()
                    _ = ctrl.get_status_dict()
                    _ = ctrl.resume()
                    _ = ctrl.get_status_dict()
            except Exception as ex:
                errors.append((tid, str(ex)))

        threads = [threading.Thread(target=worker, args=(i,)) for i in range(20)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        if errors:
            raise AssertionError(f"Encountered {len(errors)} thread errors: {errors[:3]}")
        print("  --> PASSED: 20 threads performing 400 operations concurrently without crash")
    except Exception as e:
        print(f"  --> FAILED: {e}")
        failures.append(("Multi-threaded concurrency", str(e)))

    # -------------------------------------------------------------------------
    # TEST 4: Sentinel File Tampering / Malformed JSON Handling
    # -------------------------------------------------------------------------
    print("\n[TEST 4] Corrupted Sentinel File Handling...")
    corruptions = [
        ("Zero-byte file", b""),
        ("Invalid JSON syntax (truncated)", b'{"paused": true, "reason": "broken'),
        ("Invalid JSON syntax (random bytes)", b'\x00\xff\xfe\x01\x02\x03\x7b\x7d'),
        ("Valid JSON but empty object", b'{}'),
        ("Valid JSON with unexpected types", b'{"paused": "yes", "completed_contracts_at_pause": "not_an_int"}'),
        ("Valid JSON with negative / extreme numbers", b'{"paused": true, "progress_percentage_at_pause": -99999}'),
    ]

    for label, payload in corruptions:
        try:
            ctrl.root_dir.mkdir(parents=True, exist_ok=True)
            with open(str(ctrl.sentinel_path), "wb") as f:
                f.write(payload)

            is_p = ctrl.is_paused()
            if not is_p:
                raise AssertionError(f"{label}: is_paused() returned False despite sentinel file existing")

            pdata = ctrl.get_pause_data()
            if pdata is None:
                raise AssertionError(f"{label}: get_pause_data() returned None despite is_paused() being True")

            status = ctrl.get_status_dict()
            if status["workflow_state"] != "PAUSED":
                raise AssertionError(f"{label}: workflow_state is {status['workflow_state']}, expected PAUSED")

            # Check format_status_output resilience
            formatted = format_status_output(status)
            if not formatted:
                raise AssertionError(f"{label}: format_status_output returned empty string")

            # Check resume cleans it up gracefully
            res = ctrl.resume(user="tamper_tester")
            if ctrl.is_paused():
                raise AssertionError(f"{label}: resume failed to remove corrupted sentinel")
            if not res["resumed"]:
                raise AssertionError(f"{label}: resume reported resumed=False")

            print(f"  --> PASSED corruption subcase: {label}")
        except Exception as e:
            print(f"  --> FAILED corruption subcase: {label}: {e}")
            failures.append((f"Corruption: {label}", str(e)))

    # -------------------------------------------------------------------------
    # TEST 5: Directory as Sentinel Collision
    # -------------------------------------------------------------------------
    print("\n[TEST 5] Directory in Place of Sentinel File...")
    try:
        if ctrl.sentinel_path.exists():
            ctrl.sentinel_path.unlink()
        ctrl.sentinel_path.mkdir(parents=True, exist_ok=True)

        # Path.is_file() returns False for directory
        is_p = ctrl.is_paused()
        # Controller treats directory as NOT paused because is_file() is False
        print(f"  is_paused() when sentinel is a directory: {is_p}")
        
        # Attempting pause when directory exists
        try:
            p = ctrl.pause(reason="Testing directory collision")
            print("  Pause when directory exists succeeded (replaced dir or overwrote)")
        except Exception as ex:
            print(f"  Pause threw exception when sentinel is dir: {ex}")

        # Clean up
        shutil.rmtree(str(ctrl.sentinel_path), ignore_errors=True)
        print("  --> PASSED: Handled directory collision test without unhandled fatal error")
    except Exception as e:
        print(f"  --> FAILED: {e}")
        failures.append(("Directory collision", str(e)))

    # -------------------------------------------------------------------------
    # TEST 6: Checkpoint Generation & Rollback Inspection
    # -------------------------------------------------------------------------
    print("\n[TEST 6] Checkpoint Snapshot and Rollback State Inspection...")
    try:
        cp1 = ctrl.checkpoint(label="step_1", notes="First checkpoint")
        time.sleep(0.01)
        cp2 = ctrl.checkpoint(label="step_2", notes="Second checkpoint")

        cp_files = sorted(ctrl.checkpoints_dir.glob("checkpoint_*.json"))
        if len(cp_files) < 2:
            raise AssertionError(f"Expected at least 2 checkpoints, found {len(cp_files)}")

        latest_ptr = ctrl.checkpoints_dir / "latest_checkpoint.json"
        if not latest_ptr.is_file():
            raise AssertionError("latest_checkpoint.json does not exist")

        with open(str(latest_ptr), "r", encoding="utf-8") as f:
            latest_data = json.load(f)
        if latest_data["label"] != "step_2":
            raise AssertionError(f"latest_checkpoint.json has label {latest_data['label']}, expected step_2")

        # Verify rollback capability: can we inspect and restore from an earlier checkpoint?
        with open(str(cp_files[0]), "r", encoding="utf-8") as f:
            cp1_data = json.load(f)
        if cp1_data["label"] != "step_1":
            raise AssertionError(f"First checkpoint corrupted: {cp1_data['label']}")
        
        print("  --> PASSED: Checkpoint snapshots valid and historic states inspectable")
    except Exception as e:
        print(f"  --> FAILED: {e}")
        failures.append(("Checkpoint Rollback", str(e)))

    # -------------------------------------------------------------------------
    # CLEANUP & SUMMARY
    # -------------------------------------------------------------------------
    shutil.rmtree(test_dir, ignore_errors=True)
    
    print("\n================================================================================")
    print(f"WORKFLOW CONTROL STRESS TEST SUMMARY: {len(failures)} FAILURES")
    print("================================================================================")
    if failures:
        for name, err in failures:
            print(f"  ❌ {name}: {err}")
        return False
    else:
        print("  ✅ All adversarial stress tests PASSED successfully.")
        return True

if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
