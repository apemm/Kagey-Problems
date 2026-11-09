param(
    [int]$Height = 8,
    [string]$Suffix = '',
    [string]$OutputTag = '',
    [double]$Seconds = 7200,
    [int]$StateCap = 60000000,
    [double]$MemoryMB = 20480,
    [switch]$Resume,
    [switch]$ImportPacked
)
$ErrorActionPreference = 'Stop'
$seaDirectory = $PSScriptRoot
Add-Type -Path @((Join-Path $seaDirectory 'PackedSeaStorage.cs'),
                 (Join-Path $seaDirectory 'SeaSparseStorage.cs'),
                 (Join-Path $seaDirectory 'SeaGraphSparse.cs'))
$seaStem = "sea_sparse_h$Height$Suffix$OutputTag"
$seaLog = [System.IO.StreamWriter]::new(
    (Join-Path $seaDirectory "$seaStem.log"), [bool]$Resume)
$seaLog.AutoFlush = $true
$previousOutput = [Console]::Out
[Console]::SetOut($seaLog)
try {
    $importPath = if($ImportPacked) {
        Join-Path $seaDirectory "sea_packed_h$Height$Suffix.checkpoint"
    } else { '' }
    [SeaGraphSparse]::Run(
        (Join-Path $seaDirectory "sea_residuals_h$Height$Suffix.json"),
        (Join-Path $seaDirectory "$seaStem.json"),
        $Seconds, $StateCap, $MemoryMB,
        (Join-Path $seaDirectory "$seaStem.checkpoint"),
        [bool]($Resume -or $ImportPacked),
        (Join-Path $seaDirectory "$seaStem.bin"), $importPath
    )
}
finally {
    [Console]::SetOut($previousOutput)
    $seaLog.Dispose()
}
Write-Output "Finished the sparse height-$Height$Suffix graph run."
