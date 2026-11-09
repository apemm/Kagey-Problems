param([int]$Height=32)
$ErrorActionPreference='Stop'
Add-Type -Path (Join-Path $PSScriptRoot 'ProtectedFourPressure.cs')
[ProtectedFourPressure]::Run($Height,(Join-Path $PSScriptRoot "protected_four_pressure_h$Height.json"))
