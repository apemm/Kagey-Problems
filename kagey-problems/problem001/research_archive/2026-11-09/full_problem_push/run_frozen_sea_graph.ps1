param(
    [int]$Height=8,
    [string]$Checkpoint="",
    [string]$Stem="",
    [double]$Seconds=10000,
    [double]$MemoryMB=20992,
    [string]$EndUtc="2026-11-09T18:10:00Z",
    [int]$MaxProcessed=0
)
$ErrorActionPreference='Stop'
if(-not $Checkpoint) {$Checkpoint="sea_sparse_h$Height.checkpoint"}
if(-not $Stem) {$Stem="sea_frozen_h$Height"}
Add-Type -Path (Join-Path $PSScriptRoot 'PackedSeaStorage.cs'),(Join-Path $PSScriptRoot 'SeaSparseStorage.cs'),(Join-Path $PSScriptRoot 'SeaFrozenStorage.cs'),(Join-Path $PSScriptRoot 'SeaGraphFrozen.cs')
$frozenLog=[System.IO.StreamWriter]::new((Join-Path $PSScriptRoot "$Stem.log"),$true)
$frozenLog.AutoFlush=$true
$oldOutput=[Console]::Out
[Console]::SetOut($frozenLog)
try {
    [SeaGraphFrozen]::Run(
        (Join-Path $PSScriptRoot "sea_residuals_h$Height.json"),
        (Join-Path $PSScriptRoot $Checkpoint),
        (Join-Path $PSScriptRoot "$Stem.raw"),
        (Join-Path $PSScriptRoot "$Stem.status.json"),
        $Seconds,$MemoryMB,$EndUtc,$MaxProcessed)
}
finally {[Console]::SetOut($oldOutput);$frozenLog.Dispose()}
Write-Output "Finished frozen height-$Height transitions."
