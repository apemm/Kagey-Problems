param([int]$Height=7,[int]$Span=6,[double]$Seconds=120,[int]$StateCap=2000000,
      [double]$MemoryMB=1536,[switch]$ResumeExisting)
$ErrorActionPreference='Stop'
$seaDirectory=$PSScriptRoot
Add-Type -Path @((Join-Path $seaDirectory 'PackedSeaStorage.cs'),
                 (Join-Path $seaDirectory 'SeaGraphPacked.cs'))
Add-Type -Path (Join-Path $seaDirectory 'SeaPerronExact.cs')
$manifest=Get-Content -Raw (Join-Path $seaDirectory "partition_upper_models_h${Height}_s${Span}.json") | ConvertFrom-Json
foreach($model in $manifest.models) {
    $stem="sea_packed_h$Height$($model.suffix)"
    if($ResumeExisting -and (Test-Path (Join-Path $seaDirectory "$stem.json"))) {
        $existing=Get-Content -Raw (Join-Path $seaDirectory "$stem.json") | ConvertFrom-Json
        if($existing.complete) { continue }
    }
    $log=[System.IO.StreamWriter]::new((Join-Path $seaDirectory "$stem.log"),$false)
    $log.AutoFlush=$true
    $previousOutput=[Console]::Out
    [Console]::SetOut($log)
    try {
        [SeaGraphPacked]::Run((Join-Path $seaDirectory $model.input),
            (Join-Path $seaDirectory "$stem.json"),$Seconds,$StateCap,$MemoryMB,
            (Join-Path $seaDirectory "$stem.checkpoint"),[bool]$ResumeExisting,
            (Join-Path $seaDirectory "$stem.bin"),'')
        $result=Get-Content -Raw (Join-Path $seaDirectory "$stem.json") | ConvertFrom-Json
        if($result.complete) {
            foreach($component in $result.components.cyclic_components) {
                $cid=[int]$component.id
                [SeaPerronExact]::Run((Join-Path $seaDirectory "$stem.bin"),$cid,300,120,
                    (Join-Path $seaDirectory "$stem.perron.$cid.json"),
                    (Join-Path $seaDirectory "$stem.perron.$cid.weights"))
            }
        }
    }
    finally { [Console]::SetOut($previousOutput); $log.Dispose() }
    [System.GC]::Collect()
    Write-Output "Finished upper model $stem."
}
