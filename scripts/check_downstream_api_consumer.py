#!/usr/bin/env python3
"""Compile the public QuantumFoundations facades from an external Lake package."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


SMOKE_FILES = {
    "SmokeProbability.lean": """import QuantumFoundations.ProbabilityAPI

#check QuantumFoundations.ProbabilityAPI.Perspective
#check QuantumFoundations.ProbabilityAPI.AxGrain
#check QuantumFoundations.ProbabilityAPI.grainCoherenceTheorem_projector
#check QuantumFoundations.ProbabilityAPI.EffectPerspectives.projectionEffect_weight_eq_born
""",
    "SmokeFiniteTensor.lean": """import QuantumFoundations.FiniteTensorAPI

#check QuantumFoundations.FiniteTensorAPI.TensorDecomposition
#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization
#check QuantumFoundations.FiniteTensorAPI.SystemEnvironmentFactorization
#check QuantumFoundations.FiniteTensorAPI.partialTraceEnvironment
#check QuantumFoundations.FiniteTensorAPI.tensorOperator
#check QuantumFoundations.FiniteTensorAPI.tensorOperator_smul_id_smul_id
#check QuantumFoundations.FiniteTensorAPI.tDensity

#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization.reducedSystemOperator_productProjection

#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization.reducedSystemOperator_tDensity_product
""",
    "SmokeSelectorBridge.lean": """import QuantumFoundations.SelectorBridgeAPI

#check QuantumFoundations.SelectorBridgeAPI.Selector
#check QuantumFoundations.SelectorBridgeAPI.AncillaNeutralUnder
#check QuantumFoundations.SelectorBridgeAPI.TensorMultiplicativeUnder

#check QuantumFoundations.SelectorBridgeAPI.tSelector_ancillaNeutral_iff_t_eq_one

#check QuantumFoundations.SelectorBridgeAPI.tSelectors_tensorMultiplicative_iff

#check QuantumFoundations.SelectorBridgeAPI.tSelector_sameParameterComposite_tensorMult_iff_t_eq_one

#check QuantumFoundations.SelectorBridgeAPI.tensorMultiplicative_not_implies_nsnc1
""",
    "SmokeNaimark.lean": """import QuantumFoundations.NaimarkImplementationAPI

#check QuantumFoundations.NaimarkImplementationAPI.BinaryImpl
#check QuantumFoundations.NaimarkImplementationAPI.StrictIso
#check QuantumFoundations.NaimarkImplementationAPI.minimalCore
#check QuantumFoundations.NaimarkImplementationAPI.strictIso_normalForm

#check QuantumFoundations.NaimarkImplementationAPI.residualNeutralValuationsEquivMinimalValuations

#check QuantumFoundations.NaimarkImplementationAPI.implementationIndependent_of_residualNeutral
""",
    "SmokeAggregate.lean": """import QuantumFoundations.EverettianAPI

#check QuantumFoundations.ProbabilityAPI.Perspective

#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization

#check QuantumFoundations.SelectorBridgeAPI.tSelectors_tensorMultiplicative_iff

#check QuantumFoundations.NaimarkImplementationAPI.implementationIndependent_of_residualNeutral
""",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile QuantumFoundations downstream facades externally."
    )
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--source-path", type=Path)
    source.add_argument("--git-url")
    parser.add_argument("--rev")
    parser.add_argument("--keep-temp", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    if args.git_url and not args.rev:
        parser.error("--rev is required with --git-url")
    if args.source_path is not None and args.rev is not None:
        parser.error("--rev is not allowed with --source-path")
    return args


def command_text(command: list[str]) -> str:
    return " ".join(command)


def run_checked(command: list[str], cwd: Path, *, label: str, verbose: bool, env: dict[str, str] | None = None) -> None:
    print(f"RUN [{label}]: {command_text(command)}", flush=True)
    try:
        subprocess.run(command, cwd=cwd, check=True, env=env)
    except subprocess.CalledProcessError as error:
        print(f"COMMAND_FAILED code={error.returncode}", file=sys.stderr)
        print(f"COMMAND_FAILED label={label}", file=sys.stderr)
        if verbose:
            print(f"COMMAND_FAILED cwd={cwd}", file=sys.stderr)
        raise


def toml_string(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


def toml_path(path: Path) -> str:
    return toml_string(path.resolve().as_posix())


def write_consumer_lakefile(package: Path, args: argparse.Namespace) -> None:
    if args.source_path is not None:
        dependency = f'path = "{toml_path(args.source_path)}"'
        mode = "local path"
    else:
        dependency = (
            f'git = "{toml_string(args.git_url)}"\n'
            f'rev = "{toml_string(args.rev)}"'
        )
        mode = "Git revision"
    lakefile = f'''name = "qf_downstream_smoke"
defaultTargets = ["Smoke"]

[[require]]
name = "quantum_foundations"
{dependency}

[[lean_lib]]
name = "Smoke"
globs = [
  "SmokeProbability",
  "SmokeFiniteTensor",
  "SmokeSelectorBridge",
  "SmokeNaimark",
  "SmokeAggregate"
]
'''
    (package / "lakefile.toml").write_text(lakefile, encoding="utf-8", newline="\n")
    print(f"DOWNSTREAM_CONSUMER_MODE={mode}", flush=True)


def consumer_environment(repository_root: Path) -> dict[str, str]:
    """Reuse artifacts from the checked-out revision without rebuilding it."""
    paths = [repository_root / ".lake" / "build" / "lib" / "lean"]
    packages = repository_root / ".lake" / "packages"
    if packages.is_dir():
        for package in packages.iterdir():
            paths.append(package / ".lake" / "build" / "lib" / "lean")
    environment = os.environ.copy()
    existing = environment.get("LEAN_PATH")
    lean_paths = [str(path) for path in paths if path.is_dir()]
    if existing:
        lean_paths.append(existing)
    environment["LEAN_PATH"] = os.pathsep.join(lean_paths)
    return environment


def main() -> int:
    args = parse_args()
    repository_root = Path(__file__).resolve().parents[1]
    toolchain = repository_root / "lean-toolchain"
    if not toolchain.is_file():
        print(f"missing toolchain: {toolchain}", file=sys.stderr)
        return 2

    temporary = tempfile.TemporaryDirectory(prefix="qf-downstream-smoke-")
    consumer_env = consumer_environment(repository_root)
    temporary_path = Path(temporary.name)
    package = temporary_path / "qf_downstream_smoke"
    package.mkdir()
    if args.verbose or args.keep_temp:
        print(f"DOWNSTREAM_CONSUMER_TEMP={package}", flush=True)

    try:
        shutil.copy2(toolchain, package / "lean-toolchain")
        write_consumer_lakefile(package, args)
        for filename, contents in SMOKE_FILES.items():
            (package / filename).write_text(contents, encoding="utf-8", newline="\n")

        run_checked(["lake", "update"], package, label="lake update", verbose=args.verbose)
        for filename in SMOKE_FILES:
            run_checked(
                ["lake", "env", "lean", filename],
                package,
                label=filename,
                verbose=args.verbose,
                env=consumer_env,
            )
        print("DOWNSTREAM_CONSUMER_SMOKE=PASS", flush=True)
        return 0
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"DOWNSTREAM_CONSUMER_SMOKE=FAIL ({error})", file=sys.stderr)
        if args.keep_temp or args.verbose:
            print(f"DOWNSTREAM_CONSUMER_TEMP={package}", file=sys.stderr)
        return 1
    finally:
        if args.keep_temp:
            temporary._finalizer.detach()  # type: ignore[attr-defined]
            print(f"DOWNSTREAM_CONSUMER_TEMP_KEPT={package}", flush=True)
        else:
            temporary.cleanup()


if __name__ == "__main__":
    raise SystemExit(main())
