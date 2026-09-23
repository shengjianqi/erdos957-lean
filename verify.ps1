$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'Project build failed.' }
    $taskLakeEnv = @(& lake env)
    if ($LASTEXITCODE -ne 0) { throw 'Could not read the Lake environment.' }
    $taskLeanPathLine = $taskLakeEnv | Where-Object { $_ -match '^LEAN_PATH=' } | Select-Object -First 1
    if (-not $taskLeanPathLine) { throw 'Lake did not supply LEAN_PATH.' }
    $taskPreviousLeanPath = $env:LEAN_PATH
    try {
        $env:LEAN_PATH = $taskLeanPathLine.Substring('LEAN_PATH='.Length)
        $taskLeanExecutable = (& elan which lean).Trim()
        if ($LASTEXITCODE -ne 0) { throw 'Could not locate the pinned Lean executable.' }
        & $taskLeanExecutable Audit.lean
        if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }
        & $taskLeanExecutable FinalStatementCheck.lean
        if ($LASTEXITCODE -ne 0) { throw 'Expanded statement check failed.' }
    } finally {
        $env:LEAN_PATH = $taskPreviousLeanPath
    }
} finally {
    Pop-Location
}
