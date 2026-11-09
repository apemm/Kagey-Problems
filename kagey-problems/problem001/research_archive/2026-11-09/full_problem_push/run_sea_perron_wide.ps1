param(
    [string]$Stem='sea_sparse_h8_processed_prefix',
    [int]$Component=8028601,
    [int]$Iterations=1000,
    [double]$Seconds=600,
    [string]$OutputTag='perron_wide'
)
$ErrorActionPreference='Stop'
$wideDirectory=$PSScriptRoot
Add-Type -Path (Join-Path $wideDirectory 'SeaPerronWide.cs')
Add-Type -Path (Join-Path $wideDirectory 'SeaPerronWideCheck.cs')
$wideBase=Join-Path $wideDirectory "$Stem.$OutputTag.$Component"
$wideLog=[System.IO.StreamWriter]::new("$wideBase.log",$false)
$wideLog.AutoFlush=$true
$widePreviousOutput=[Console]::Out
[Console]::SetOut($wideLog)
try {
    [SeaPerronWide]::Run((Join-Path $wideDirectory "$Stem.bin"),$Component,$Iterations,$Seconds,
        "$wideBase.json","$wideBase.weights")
    [SeaPerronWideCheck]::Run((Join-Path $wideDirectory "$Stem.bin"),"$wideBase.weights","$wideBase.check.json")
}
finally {[Console]::SetOut($widePreviousOutput);$wideLog.Dispose()}
Write-Output "Finished wide integer certificate and independent direct-graph check."
