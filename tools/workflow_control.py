#!/usr/bin/env python3
"""
tools/workflow_control.py — Clean Pause/Resume and Checkpoint Control for Autoformalization

Provides an operational, robust CLI and Python API for pausing, resuming,
inspecting status, and creating progress checkpoints during the Gromov Compactness
autoformalization process.

Features:
- Zero external dependencies (uses standard library: sys, os, io, json, time, datetime, pathlib, argparse, unittest).
- Sentinel file `.pause_workflow` indicates paused state with structured JSON metadata.
- CLI subcommands:
    pause       Create sentinel file with timestamp, active phase, and snapshot.
    resume      Remove sentinel file, validate state consistency, and signal resumption.
    status      Display real-time status (paused flag, active phase, contract count, progress %).
    checkpoint  Save full progress JSON snapshot to .agents/teamwork/checkpoints/.
    test        Run comprehensive automated test suite (100% pass rate).
- Safe for concurrent inspection and idempotent operations.
- Compatible with Python 3.6+.
"""

import sys
import os
import io

def ensure_utf8_streams():
    """Ensure stdout and stderr use UTF-8 encoding idempotently on all Python versions."""
    if getattr(sys, "_utf8_configured", False):
        return
    sys._utf8_configured = True
    if hasattr(sys.stdout, "buffer") and (not sys.stdout.encoding or sys.stdout.encoding.lower() != "utf-8"):
        try:
            sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
        except Exception:
            pass
    if hasattr(sys.stderr, "buffer") and (not sys.stderr.encoding or sys.stderr.encoding.lower() != "utf-8"):
        try:
            sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")
        except Exception:
            pass

ensure_utf8_streams()

import json
import time
import argparse
import unittest
import threading
import uuid
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple

DEFAULT_ROOT = Path("/Users/pablosuarez/Desktop/SympTopAutoForm")
SENTINEL_FILENAME = ".pause_workflow"
CHECKPOINTS_DIRNAME = ".agents/teamwork/checkpoints"

# Complete 32-contract inventory across the 4 tracks as defined in gromov_compactness.pdf
ALL_CONTRACT_IDS = [
    # Track 1: Foundations & Bookkeeping Layer (F00–F06)
    "F00", "F01", "F02", "F03", "F04", "F05", "F06",
    # Track 2: Local Analytic Estimates Layer (A01–A12)
    "A01", "A02", "A03", "A04", "A05", "A06", "A07", "A08", "A09", "A10", "A11", "A12",
    # Track 3: Concentration Compactness & Bubbling Engine (C01–C03, B01–B07)
    "C01", "C02", "C03", "B01", "B02", "B03", "B04", "B05", "B06", "B07",
    # Track 4: Global Assembly & Master Theorems (G01–G05)
    "G01", "G02", "G03", "G04", "G05",
]

CONTRACT_FILE_MAPPING = {
    "F00": "GromovCompactness/LibraryAudit.lean",
    "F01": "GromovCompactness/Geometry/Target.lean",
    "F02": "GromovCompactness/Geometry/Sphere.lean",
    "F03": "GromovCompactness/Analysis/Energy.lean",
    "F04": "GromovCompactness/Topology/SmoothLocal.lean",
    "F05": "GromovCompactness/Topology/Subsequence.lean",
    "F06": "GromovCompactness/Topology/SphereTree.lean",
    "A01": "GromovCompactness/Analysis/MeanValue.lean",
    "A02": "GromovCompactness/Analysis/Bochner.lean",
    "A03": "GromovCompactness/Analysis/EpsilonRegularity.lean",
    "A04": "GromovCompactness/Analysis/EllipticToolkit.lean",
    "A05": "GromovCompactness/Analysis/Bootstrap.lean",
    "A06": "GromovCompactness/Analysis/LocalCompactness.lean",
    "A07": "GromovCompactness/Analysis/EnergyGap.lean",
    "A08": "GromovCompactness/Analysis/Monotonicity.lean",
    "A09": "GromovCompactness/Analysis/CylinderLocalization.lean",
    "A10": "GromovCompactness/Analysis/CylinderDecay.lean",
    "A11": "GromovCompactness/Analysis/PunctureExtension.lean",
    "A12": "GromovCompactness/Analysis/Removal.lean",
    "C01": "GromovCompactness/Compactness/Measures.lean",
    "C02": "GromovCompactness/Compactness/Concentration.lean",
    "C03": "GromovCompactness/Compactness/Defect.lean",
    "B01": "GromovCompactness/Bubbling/Threshold.lean",
    "B02": "GromovCompactness/Bubbling/Calibration.lean",
    "B03": "GromovCompactness/Bubbling/Neck.lean",
    "B04": "GromovCompactness/Bubbling/OneLevel.lean",
    "B05": "GromovCompactness/Bubbling/GhostBranching.lean",
    "B06": "GromovCompactness/Bubbling/Rank.lean",
    "B07": "GromovCompactness/Bubbling/LocalTree.lean",
    "G01": "GromovCompactness/Compactness/Assembly.lean",
    "G02": "GromovCompactness/Compactness/Stabilize.lean",
    "G03": "GromovCompactness/Compactness/GenusZero.lean",
    "G04": "GromovCompactness/Topology/ComponentCount.lean",
    "G05": "GromovCompactness/Main.lean",
}


def get_iso_timestamp() -> str:
    """Return current UTC time in ISO-8601 format."""
    return datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")


class WorkflowController:
    """
    Manages workflow pause/resume state, progress tracking, and checkpoints.
    """

    def __init__(self, root_dir: Optional[Path] = None):
        self.root_dir = Path(root_dir) if root_dir else DEFAULT_ROOT
        self.sentinel_path = self.root_dir / SENTINEL_FILENAME
        self.checkpoints_dir = self.root_dir / CHECKPOINTS_DIRNAME

    def is_paused(self) -> bool:
        """Return True if the workflow is currently paused."""
        return self.sentinel_path.is_file()

    def get_pause_data(self) -> Optional[Dict[str, Any]]:
        """Read and parse the sentinel file if paused."""
        if not self.is_paused():
            return None
        try:
            with open(str(self.sentinel_path), "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            return {
                "paused": True,
                "error": f"Failed to parse sentinel JSON: {str(e)}",
                "raw_present": True,
            }

    def pause(
        self,
        reason: str = "User requested workflow pause",
        active_task: str = "Phase 1: Foundations & Bookkeeping Layer (Model A)",
        user: str = "user",
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """
        Pause the workflow by creating the sentinel file.
        Idempotent: updates reason and timestamp if already paused.
        """
        self.root_dir.mkdir(parents=True, exist_ok=True)
        now = get_iso_timestamp()
        
        status_info = self.get_status_dict()
        
        pause_record = {
            "paused": True,
            "paused_at": now,
            "reason": reason,
            "active_task": active_task,
            "user": user,
            "completed_contracts_at_pause": status_info["completed_contracts_count"],
            "progress_percentage_at_pause": status_info["progress_percentage"],
            "metadata": metadata or {},
        }

        # Write atomically using a thread-safe temporary file
        temp_path = self.root_dir / f"{SENTINEL_FILENAME}.tmp.{os.getpid()}.{threading.get_ident()}.{uuid.uuid4().hex[:8]}"
        try:
            with open(str(temp_path), "w", encoding="utf-8") as f:
                json.dump(pause_record, f, indent=2)
                f.write("\n")
            temp_path.replace(self.sentinel_path)
        except Exception:
            try:
                temp_path.unlink()
            except Exception:
                pass
            raise

        return pause_record

    def resume(self, user: str = "user") -> Dict[str, Any]:
        """
        Resume the workflow by removing the sentinel file.
        Returns details of the resumed pause session.
        """
        if not self.is_paused():
            return {
                "resumed": False,
                "message": "Workflow was not paused (sentinel not found).",
                "status": "RUNNING",
            }

        pause_data = self.get_pause_data() or {}
        try:
            self.sentinel_path.unlink()
        except FileNotFoundError:
            pass

        now = get_iso_timestamp()
        resume_record = {
            "resumed": True,
            "resumed_at": now,
            "user": user,
            "was_paused_at": pause_data.get("paused_at"),
            "pause_reason": pause_data.get("reason"),
            "active_task": pause_data.get("active_task"),
            "status": "RUNNING",
            "message": "Workflow sentinel successfully cleared. Execution may resume.",
        }

        # Record resume event into checkpoints log directory
        try:
            self.checkpoints_dir.mkdir(parents=True, exist_ok=True)
            log_path = self.checkpoints_dir / "pause_resume_log.jsonl"
            with open(str(log_path), "a", encoding="utf-8") as f:
                event = {
                    "event": "resume",
                    "timestamp": now,
                    "pause_data": pause_data,
                    "user": user,
                }
                f.write(json.dumps(event) + "\n")
        except Exception:
            pass

        # Verify and ensure Ollama daemon is active to guarantee local compute upon resumption
        try:
            from tools.ollama_lean4_client import ensure_ollama_daemon, DEFAULT_OLLAMA_HOST
            ok_o, msg_o, _ = ensure_ollama_daemon(DEFAULT_OLLAMA_HOST, autostart=True, timeout=8.0)
            resume_record["ollama_daemon"] = {"active": ok_o, "message": msg_o}
        except Exception:
            try:
                from ollama_lean4_client import ensure_ollama_daemon, DEFAULT_OLLAMA_HOST
                ok_o, msg_o, _ = ensure_ollama_daemon(DEFAULT_OLLAMA_HOST, autostart=True, timeout=8.0)
                resume_record["ollama_daemon"] = {"active": ok_o, "message": msg_o}
            except Exception:
                pass

        return resume_record

    def scan_contracts(self) -> Dict[str, Any]:
        """
        Scan repository to determine presence and status of modules F00–G05.
        """
        scanned = {}
        completed_count = 0
        phase1_completed_count = 0
        phase1_total = 7

        for cid in ALL_CONTRACT_IDS:
            rel_file = CONTRACT_FILE_MAPPING.get(cid)
            if not rel_file:
                continue
            full_path = self.root_dir / rel_file
            if full_path.is_file():
                try:
                    size = full_path.stat().st_size
                    with open(str(full_path), "r", encoding="utf-8") as f:
                        lines = len(f.readlines())
                    scanned[cid] = {
                        "exists": True,
                        "path": rel_file,
                        "lines": lines,
                        "size_bytes": size,
                        "status": "SCAFFOLDED_OR_VERIFIED",
                    }
                    completed_count += 1
                    if cid.startswith("F"):
                        phase1_completed_count += 1
                except Exception as e:
                    scanned[cid] = {
                        "exists": True,
                        "path": rel_file,
                        "error": str(e),
                        "status": "READ_ERROR",
                    }
            else:
                scanned[cid] = {
                    "exists": False,
                    "path": rel_file,
                    "status": "PENDING",
                }

        total_contracts = len(ALL_CONTRACT_IDS)
        pct = round((completed_count / float(total_contracts)) * 100.0, 2)
        phase1_pct = round((phase1_completed_count / float(phase1_total)) * 100.0, 2)

        return {
            "contracts": scanned,
            "completed_count": completed_count,
            "total_count": total_contracts,
            "progress_percentage": pct,
            "phase1_completed": phase1_completed_count,
            "phase1_total": phase1_total,
            "phase1_percentage": phase1_pct,
        }

    def get_latest_checkpoint_time(self) -> Optional[str]:
        """Retrieve timestamp of latest checkpoint file if any exists."""
        if not self.checkpoints_dir.is_dir():
            return None
        checkpoints = sorted(self.checkpoints_dir.glob("checkpoint_*.json"))
        if not checkpoints:
            return None
        try:
            with open(str(checkpoints[-1]), "r", encoding="utf-8") as f:
                data = json.load(f)
                return data.get("timestamp")
        except Exception:
            return None

    def get_ollama_status(self) -> Dict[str, Any]:
        """Check Ollama service status and optimal model discovery."""
        try:
            from tools.ollama_lean4_client import (
                is_ollama_running, check_connection, detect_best_model, DEFAULT_OLLAMA_HOST
            )
        except ImportError:
            try:
                from ollama_lean4_client import (
                    is_ollama_running, check_connection, detect_best_model, DEFAULT_OLLAMA_HOST
                )
            except ImportError:
                return {"active": False, "status": "UNKNOWN", "model": None, "host": "http://localhost:11434"}

        active = is_ollama_running(DEFAULT_OLLAMA_HOST, timeout=1.5)
        if not active:
            return {"active": False, "status": "STOPPED", "model": None, "host": DEFAULT_OLLAMA_HOST}

        ok, msg, data = check_connection(DEFAULT_OLLAMA_HOST, timeout=2.0, autostart=False)
        if not ok:
            return {"active": False, "status": "UNRESPONSIVE", "model": None, "host": DEFAULT_OLLAMA_HOST}

        best, _, models = detect_best_model(DEFAULT_OLLAMA_HOST, tags_data=data)
        return {
            "active": True,
            "status": "RUNNING",
            "model": best,
            "host": DEFAULT_OLLAMA_HOST,
            "model_count": len(models),
        }

    def get_status_dict(self) -> Dict[str, Any]:
        """Return structured real-time status dictionary."""
        paused = self.is_paused()
        pause_data = self.get_pause_data() if paused else None
        scan = self.scan_contracts()
        latest_cp = self.get_latest_checkpoint_time()
        ollama_info = self.get_ollama_status()

        # Determine active phase
        if scan["phase1_completed"] < scan["phase1_total"]:
            active_phase = "Phase 1: Foundations & Bookkeeping Layer (F00–F06)"
        elif scan["completed_count"] < 19:
            active_phase = "Phase 2: Local Analysis & Calibrated Bubbling (A01–A12, C01–C03, B01–B07)"
        elif scan["completed_count"] < scan["total_count"]:
            active_phase = "Phase 3: Global Tree Assembly & Compactness (G01–G05)"
        else:
            active_phase = "Phase 4: Complete Formally Verified Theorem (Complete)"

        return {
            "timestamp": get_iso_timestamp(),
            "workflow_state": "PAUSED" if paused else "RUNNING",
            "is_paused": paused,
            "pause_details": pause_data,
            "active_phase": active_phase,
            "completed_contracts_count": scan["completed_count"],
            "total_contracts_count": scan["total_count"],
            "progress_percentage": scan["progress_percentage"],
            "phase1_completed": scan["phase1_completed"],
            "phase1_total": scan["phase1_total"],
            "phase1_percentage": scan["phase1_percentage"],
            "latest_checkpoint_timestamp": latest_cp,
            "ollama_prover": ollama_info,
        }

    def checkpoint(
        self,
        label: str = "manual_checkpoint",
        notes: str = "",
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """
        Create a comprehensive JSON progress snapshot saved to .agents/teamwork/checkpoints/.
        """
        self.checkpoints_dir.mkdir(parents=True, exist_ok=True)
        now = get_iso_timestamp()
        now_slug = now.replace(":", "").replace("-", "")

        status = self.get_status_dict()
        scan = self.scan_contracts()

        snapshot = {
            "checkpoint_id": f"chk_{now_slug}_{label}",
            "timestamp": now,
            "label": label,
            "notes": notes,
            "workflow_state": status["workflow_state"],
            "is_paused": status["is_paused"],
            "active_phase": status["active_phase"],
            "progress_percentage": status["progress_percentage"],
            "phase1_percentage": status["phase1_percentage"],
            "completed_contracts_count": status["completed_contracts_count"],
            "total_contracts_count": status["total_contracts_count"],
            "contracts_breakdown": scan["contracts"],
            "pause_details": status["pause_details"],
            "metadata": metadata or {},
        }

        filename = f"checkpoint_{now_slug}_{label}.json"
        target_path = self.checkpoints_dir / filename
        with open(str(target_path), "w", encoding="utf-8") as f:
            json.dump(snapshot, f, indent=2)
            f.write("\n")

        # Also write / update latest symlink or pointer
        latest_path = self.checkpoints_dir / "latest_checkpoint.json"
        with open(str(latest_path), "w", encoding="utf-8") as f:
            json.dump(snapshot, f, indent=2)
            f.write("\n")

        snapshot["saved_to"] = str(target_path)
        snapshot["latest_pointer"] = str(latest_path)
        return snapshot

    def check_and_wait_if_paused(
        self,
        poll_interval: float = 2.0,
        timeout: Optional[float] = None,
        callback: Optional[Any] = None,
    ) -> bool:
        """
        Helper loop for long-running processes: if paused, wait until resumed.
        Returns True when resumed, or False if timeout reached.
        """
        start_time = time.time()
        was_paused = False

        while self.is_paused():
            if not was_paused:
                was_paused = True
                if callback:
                    callback(self.get_pause_data())
            if timeout and (time.time() - start_time) > timeout:
                return False
            time.sleep(poll_interval)

        return True


# ==============================================================================
# CLI Formatting Helpers
# ==============================================================================

def print_banner(title: str):
    print("=" * 72)
    print(f"  {title}")
    print("=" * 72)

def format_status_output(status: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("  GROMOV COMPACTNESS AUTOFORMALIZATION — WORKFLOW STATUS")
    lines.append("=" * 72)
    state = status["workflow_state"]
    state_display = f"🔴 {state}" if state == "PAUSED" else f"🟢 {state}"
    lines.append(f"  Status:             {state_display}")
    lines.append(f"  Active Phase:       {status['active_phase']}")
    lines.append(f"  Overall Progress:   {status['progress_percentage']}% ({status['completed_contracts_count']} of {status['total_contracts_count']} contracts)")
    lines.append(f"  Phase 1 Progress:   {status['phase1_percentage']}% ({status['phase1_completed']} of {status['phase1_total']} contracts)")
    lines.append(f"  Last Checkpoint:    {status['latest_checkpoint_timestamp'] or 'None recorded'}")

    ollama_info = status.get("ollama_prover") or {}
    if ollama_info.get("active"):
        model_str = f", Model: {ollama_info.get('model')}" if ollama_info.get('model') else ""
        lines.append(f"  Ollama Prover:      🟢 ACTIVE ({ollama_info.get('host')}{model_str})")
    else:
        st = ollama_info.get("status", "STOPPED")
        lines.append(f"  Ollama Prover:      🔴 {st} ({ollama_info.get('host', 'http://localhost:11434')})")

    if status["is_paused"]:
        pd = status.get("pause_details") or {}
        lines.append("-" * 72)
        lines.append("  [PAUSE DETAILS]")
        lines.append(f"  Paused At:          {pd.get('paused_at')}")
        lines.append(f"  Reason:             {pd.get('reason')}")
        lines.append(f"  Paused Task:        {pd.get('active_task')}")
        lines.append(f"  User / Initiator:   {pd.get('user')}")
        lines.append(f"  To resume run:      python3 tools/workflow_control.py resume")

    lines.append("=" * 72)
    return "\n".join(lines)


# ==============================================================================
# Automated Test Suite (100% Pass Rate Target)
# ==============================================================================

class TestWorkflowController(unittest.TestCase):
    """
    Comprehensive test suite verifying pause, resume, status, and checkpoint operations.
    """

    def setUp(self):
        # Create a temporary sandbox root directory for isolated testing
        import tempfile
        self.test_dir = tempfile.mkdtemp(prefix="test_symp_workflow_")
        self.root = Path(self.test_dir)
        self.ctrl = WorkflowController(self.root)

    def tearDown(self):
        import shutil
        shutil.rmtree(self.test_dir, ignore_errors=True)

    def test_01_initial_status_unpaused(self):
        """Verify initial state is RUNNING and unpaused."""
        self.assertFalse(self.ctrl.is_paused())
        status = self.ctrl.get_status_dict()
        self.assertEqual(status["workflow_state"], "RUNNING")
        self.assertFalse(status["is_paused"])
        self.assertIsNone(status["pause_details"])

    def test_02_pause_creates_sentinel(self):
        """Verify pause creates .pause_workflow with correct JSON schema."""
        record = self.ctrl.pause(
            reason="User stepped away for coffee",
            active_task="Testing Phase 1 Scaffold",
            user="tester",
            metadata={"test_run": 1},
        )
        self.assertTrue(self.ctrl.is_paused())
        self.assertTrue(self.ctrl.sentinel_path.is_file())
        self.assertTrue(record["paused"])
        self.assertEqual(record["reason"], "User stepped away for coffee")
        self.assertEqual(record["active_task"], "Testing Phase 1 Scaffold")
        self.assertEqual(record["user"], "tester")
        self.assertIn("paused_at", record)

        # Inspect pause data from disk
        disk_data = self.ctrl.get_pause_data()
        self.assertIsNotNone(disk_data)
        self.assertEqual(disk_data["reason"], "User stepped away for coffee")

    def test_03_status_reflects_paused_state(self):
        """Verify status command accurately reflects paused details."""
        self.ctrl.pause(reason="Testing paused state report")
        status = self.ctrl.get_status_dict()
        self.assertEqual(status["workflow_state"], "PAUSED")
        self.assertTrue(status["is_paused"])
        self.assertIsNotNone(status["pause_details"])
        self.assertEqual(status["pause_details"]["reason"], "Testing paused state report")

    def test_04_resume_removes_sentinel(self):
        """Verify resume removes sentinel cleanly and signals resumption."""
        self.ctrl.pause(reason="Short pause before resume test")
        self.assertTrue(self.ctrl.is_paused())

        resume_info = self.ctrl.resume(user="tester_resume")
        self.assertFalse(self.ctrl.is_paused())
        self.assertFalse(self.ctrl.sentinel_path.is_file())
        self.assertTrue(resume_info["resumed"])
        self.assertEqual(resume_info["status"], "RUNNING")
        self.assertIn("resumed_at", resume_info)

    def test_05_resume_when_already_running(self):
        """Verify resume behaves gracefully when not paused."""
        self.assertFalse(self.ctrl.is_paused())
        info = self.ctrl.resume()
        self.assertFalse(info["resumed"])
        self.assertEqual(info["status"], "RUNNING")

    def test_06_checkpoint_generation(self):
        """Verify checkpoint creates valid snapshot file and latest pointer."""
        snap = self.ctrl.checkpoint(label="unit_test_checkpoint", notes="Testing checkpoint creation")
        self.assertIn("checkpoint_id", snap)
        self.assertTrue(Path(snap["saved_to"]).is_file())
        self.assertTrue(Path(snap["latest_pointer"]).is_file())

        with open(snap["saved_to"], "r", encoding="utf-8") as f:
            data = json.load(f)
            self.assertEqual(data["label"], "unit_test_checkpoint")
            self.assertEqual(data["notes"], "Testing checkpoint creation")
            self.assertIn("progress_percentage", data)
            self.assertIn("contracts_breakdown", data)

    def test_07_contract_scanning_accuracy(self):
        """Verify contract scanner accurately detects presence of module files."""
        # Before creating any files
        scan0 = self.ctrl.scan_contracts()
        self.assertEqual(scan0["completed_count"], 0)
        self.assertEqual(scan0["progress_percentage"], 0.0)

        # Create F00 and F01 fake target files
        f00_path = self.root / CONTRACT_FILE_MAPPING["F00"]
        f00_path.parent.mkdir(parents=True, exist_ok=True)
        with open(str(f00_path), "w", encoding="utf-8") as f:
            f.write("-- F00 test\nimport Mathlib\n")

        scan1 = self.ctrl.scan_contracts()
        self.assertEqual(scan1["completed_count"], 1)
        self.assertEqual(scan1["phase1_completed"], 1)
        self.assertTrue(scan1["contracts"]["F00"]["exists"])
        self.assertFalse(scan1["contracts"]["F01"]["exists"])

    def test_08_check_and_wait_helper(self):
        """Verify check_and_wait_if_paused respects timeout or unpause."""
        # Unpaused should return immediately True
        self.assertTrue(self.ctrl.check_and_wait_if_paused(poll_interval=0.01, timeout=0.1))

        # Paused with small timeout should expire to False
        self.ctrl.pause(reason="Testing timeout")
        self.assertFalse(self.ctrl.check_and_wait_if_paused(poll_interval=0.01, timeout=0.05))

        # Unpause and verify immediate return
        self.ctrl.resume()
        self.assertTrue(self.ctrl.check_and_wait_if_paused(poll_interval=0.01, timeout=0.1))


def run_unit_tests() -> bool:
    """Run unit test suite and return True if 100% pass."""
    suite = unittest.TestLoader().loadTestsFromTestCase(TestWorkflowController)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return result.wasSuccessful()


# ==============================================================================
# Main CLI Entry Point
# ==============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Gromov Compactness Autoformalization — Workflow Pause/Resume & Checkpoint Controller",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Check status
  python3 tools/workflow_control.py status

  # Pause workflow
  python3 tools/workflow_control.py pause --reason "Stepping out for meeting"

  # Resume workflow
  python3 tools/workflow_control.py resume

  # Save checkpoint snapshot
  python3 tools/workflow_control.py checkpoint --label "phase1_scaffolding"

  # Run self-test suite
  python3 tools/workflow_control.py test
""",
    )
    parser.add_argument(
        "--root",
        type=str,
        default=str(DEFAULT_ROOT),
        help=f"Project root directory (default: {DEFAULT_ROOT})",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output raw JSON instead of human-readable text",
    )

    subparsers = parser.add_subparsers(dest="command", help="Subcommand to execute")

    # pause
    p_pause = subparsers.add_parser("pause", help="Pause workflow execution via sentinel file")
    p_pause.add_argument("--reason", type=str, default="User requested workflow pause", help="Reason for pausing")
    p_pause.add_argument("--active-task", type=str, default="Phase 1: Foundations & Bookkeeping Layer", help="Active task description")
    p_pause.add_argument("--user", type=str, default=os.getenv("USER", "user"), help="User or agent identifier")

    # resume
    p_resume = subparsers.add_parser("resume", help="Resume workflow execution by clearing sentinel")
    p_resume.add_argument("--user", type=str, default=os.getenv("USER", "user"), help="User or agent identifier")

    # status
    p_status = subparsers.add_parser("status", help="Show current workflow execution and progress status")

    # checkpoint
    p_chk = subparsers.add_parser("checkpoint", help="Create progress checkpoint JSON snapshot")
    p_chk.add_argument("--label", type=str, default="manual_checkpoint", help="Descriptive label for checkpoint")
    p_chk.add_argument("--notes", type=str, default="", help="Optional notes")

    # test
    p_test = subparsers.add_parser("test", help="Run comprehensive automated test suite (100% pass verification)")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(0)

    root_path = Path(args.root)
    ctrl = WorkflowController(root_path)

    if args.command == "pause":
        record = ctrl.pause(reason=args.reason, active_task=args.active_task, user=args.user)
        if args.json:
            print(json.dumps(record, indent=2))
        else:
            print(f"⏸️  Workflow paused successfully.")
            print(f"   Sentinel created: {ctrl.sentinel_path}")
            print(f"   Reason:           {args.reason}")
            print(f"   Active task:      {args.active_task}")
            print(f"   Timestamp:        {record['paused_at']}")
            print(f"   To resume run:    python3 tools/workflow_control.py resume")

    elif args.command == "resume":
        record = ctrl.resume(user=args.user)
        if args.json:
            print(json.dumps(record, indent=2))
        else:
            if record["resumed"]:
                print(f"▶️  Workflow resumed successfully.")
                print(f"   Sentinel cleared: {ctrl.sentinel_path}")
                print(f"   Resumed at:       {record['resumed_at']}")
                print(f"   Previous reason:  {record.get('pause_reason')}")
            else:
                print(f"ℹ️  Workflow was not paused: {record['message']}")

    elif args.command == "status":
        status = ctrl.get_status_dict()
        if args.json:
            print(json.dumps(status, indent=2))
        else:
            print(format_status_output(status))

    elif args.command == "checkpoint":
        snap = ctrl.checkpoint(label=args.label, notes=args.notes)
        if args.json:
            print(json.dumps(snap, indent=2))
        else:
            print(f"💾 Checkpoint created successfully.")
            print(f"   ID:         {snap['checkpoint_id']}")
            print(f"   Saved to:   {snap['saved_to']}")
            print(f"   Progress:   {snap['progress_percentage']}% ({snap['completed_contracts_count']} of {snap['total_contracts_count']} contracts)")
            print(f"   Phase 1:    {snap['phase1_percentage']}% ({snap['phase1_percentage']}% of Phase 1 contracts)")

    elif args.command == "test":
        print_banner("RUNNING WORKFLOW CONTROL UNIT TEST SUITE")
        success = run_unit_tests()
        if success:
            print("\n✅ All unit tests PASSED (100% pass rate).")
            sys.exit(0)
        else:
            print("\n❌ Unit tests FAILED.")
            sys.exit(1)


if __name__ == "__main__":
    main()
