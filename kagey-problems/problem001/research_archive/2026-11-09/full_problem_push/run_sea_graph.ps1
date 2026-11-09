param(
    [int]$Height = 7,
    [double]$Seconds = 3600,
    [int]$StateCap = 10000000,
    [double]$MemoryMB = 4096,
    [switch]$Resume
)
$ErrorActionPreference = 'Stop'
$seaDirectory = $PSScriptRoot
Add-Type -Path (Join-Path $seaDirectory 'SeaGraphExact.cs')
$seaLog = [System.IO.StreamWriter]::new(
    (Join-Path $seaDirectory "sea_csharp_h$Height.log"), [bool]$Resume)
$seaLog.AutoFlush = $true
$previousOutput = [Console]::Out
[Console]::SetOut($seaLog)
try {
    [SeaGraphExact]::Run(
        (Join-Path $seaDirectory "sea_residuals_h$Height.json"),
        (Join-Path $seaDirectory "sea_csharp_h$Height.json"),
        $Seconds, $StateCap, $MemoryMB,
        (Join-Path $seaDirectory "sea_csharp_h$Height.checkpoint"),
        [bool]$Resume,
        (Join-Path $seaDirectory "sea_csharp_h$Height.bin")
    )
}
finally {
    [Console]::SetOut($previousOutput)
    $seaLog.Dispose()
}
Write-Output "Finished the height-$Height exact graph run."
