param(
    [int]$Height = 7,
    [string]$Suffix = '',
    [double]$Seconds = 3600,
    [int]$StateCap = 40000000,
    [double]$MemoryMB = 6144,
    [switch]$Resume,
    [switch]$ImportLegacy
)
$ErrorActionPreference = 'Stop'
$seaDirectory = $PSScriptRoot
Add-Type -Path @((Join-Path $seaDirectory 'PackedSeaStorage.cs'),
                 (Join-Path $seaDirectory 'SeaGraphPacked.cs'))
$seaStem = "sea_packed_h$Height$Suffix"
$seaLog = [System.IO.StreamWriter]::new(
    (Join-Path $seaDirectory "$seaStem.log"), [bool]$Resume)
$seaLog.AutoFlush = $true
$previousOutput = [Console]::Out
[Console]::SetOut($seaLog)
try {
    $legacyPath = if($ImportLegacy) {
        Join-Path $seaDirectory "sea_csharp_h$Height$Suffix.checkpoint"
    } else { '' }
    [SeaGraphPacked]::Run(
        (Join-Path $seaDirectory "sea_residuals_h$Height$Suffix.json"),
        (Join-Path $seaDirectory "$seaStem.json"),
        $Seconds, $StateCap, $MemoryMB,
        (Join-Path $seaDirectory "$seaStem.checkpoint"),
        [bool]$Resume,
        (Join-Path $seaDirectory "$seaStem.bin"), $legacyPath
    )
}
finally {
    [Console]::SetOut($previousOutput)
    $seaLog.Dispose()
}
Write-Output "Finished the packed height-$Height$Suffix graph run."
