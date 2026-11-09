param(
    [string]$Stem = 'sea_packed_h7',
    [int]$Component = -1,
    [int]$Iterations = 1000,
    [double]$Seconds = 1800
)
$ErrorActionPreference='Stop'
$seaDirectory=$PSScriptRoot
if($Component -lt 0) {
    $seaResult=Get-Content -Raw (Join-Path $seaDirectory "$Stem.json") | ConvertFrom-Json
    if(-not $seaResult.complete) { throw 'Graph is incomplete' }
    $Component=[int]$seaResult.components.cyclic_components[0].id
}
Add-Type -Path (Join-Path $seaDirectory 'SeaPerronExact.cs')
$seaLog=[System.IO.StreamWriter]::new((Join-Path $seaDirectory "$Stem.perron.$Component.log"),$false)
$seaLog.AutoFlush=$true
$previousOutput=[Console]::Out
[Console]::SetOut($seaLog)
try {
    [SeaPerronExact]::Run(
        (Join-Path $seaDirectory "$Stem.bin"),$Component,$Iterations,$Seconds,
        (Join-Path $seaDirectory "$Stem.perron.$Component.json"),
        (Join-Path $seaDirectory "$Stem.perron.$Component.weights"))
}
finally { [Console]::SetOut($previousOutput); $seaLog.Dispose() }
Write-Output "Finished exact Perron enclosure for $Stem component $Component."
