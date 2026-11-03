#!/usr/bin/env python3
"""
test_multiprocess_concurrency.py — Test multi-process concurrency on tools/workflow_control.py
"""
import os
import sys
import time
import tempfile
import shutil
import multiprocessing
from pathlib import Path

sys.path.insert(0, "/Users/pablosuarez/Desktop/SympTopAutoForm")
from tools.workflow_control import WorkflowController

def process_worker(root_str, proc_id, iterations, error_queue):
    ctrl = WorkflowController(Path(root_str))
    try:
        for i in range(iterations):
            ctrl.pause(reason=f"Proc {proc_id} iter {i}")
            _ = ctrl.is_paused()
            _ = ctrl.get_status_dict()
            ctrl.resume(user=f"proc_{proc_id}")
            _ = ctrl.get_status_dict()
    except Exception as ex:
        error_queue.put((proc_id, str(ex)))

def main():
    test_dir = tempfile.mkdtemp(prefix="adv_test_proc_")
    error_queue = multiprocessing.Queue()
    num_procs = 8
    iters = 25

    processes = [
        multiprocessing.Process(
            target=process_worker,
            args=(test_dir, p, iters, error_queue),
        )
        for p in range(num_procs)
    ]

    for p in processes:
        p.start()
    for p in processes:
        p.join()

    errors = []
    while not error_queue.empty():
        errors.append(error_queue.get())

    shutil.rmtree(test_dir, ignore_errors=True)

    if errors:
        print(f"Multi-process concurrency FAILED with {len(errors)} errors: {errors[:3]}")
        sys.exit(1)
    else:
        print("Multi-process concurrency PASSED (8 processes x 25 cycles = 200 cycles).")
        sys.exit(0)

if __name__ == "__main__":
    main()
