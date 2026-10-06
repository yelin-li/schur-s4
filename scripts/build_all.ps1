# Builds the whole development, including the three exhaustive branches.
#
# The three branches are independent Lean files, so they are built in parallel
# as separate processes (lake would also parallelise them, but running them
# explicitly makes the timing visible).
#
# Usage:  pwsh -File scripts/build_all.ps1

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $root

Write-Host "== kernel-checked core =="
lake build Schur Symmetry RuleB

Write-Host "== exhaustive branches (parallel) =="
$targets = @(
    @{ Name = "BranchB0"; Seconds = 0 },
    @{ Name = "BranchB1"; Seconds = 0 },
    @{ Name = "BranchB2"; Seconds = 0 }
)

$jobs = foreach ($t in $targets) {
    $name = $t.Name
    Start-Job -ScriptBlock {
        param($dir, $mod)
        Set-Location $dir
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        & lake env lean -o ".lake/build/lib/lean/$mod.olean" "$mod.lean"
        if ($LASTEXITCODE -ne 0) { throw "$mod failed" }
        $sw.Stop()
        [pscustomobject]@{ Module = $mod; Seconds = [math]::Round($sw.Elapsed.TotalSeconds) }
    } -ArgumentList $root, $name
}

$results = $jobs | Wait-Job | Receive-Job
$jobs | Remove-Job
$results | Sort-Object Module | Format-Table -AutoSize
$results | ForEach-Object { "$($_.Module) $($_.Seconds)s" } |
    Set-Content -Path "bench/branch_timings.txt"

Write-Host "== assembly =="
lake env lean -o ".lake/build/lib/lean/S4.olean" "S4.lean"
lake env lean "Verify.lean"

Write-Host ""
Write-Host "Done. The main results are:"
Write-Host "  Schur.no_good_four_45  : no 4-colouring of {1,...,45} is sum-free"
Write-Host "  Schur.four_colors_exact: S(4) = 44"
