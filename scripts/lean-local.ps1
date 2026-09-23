#requires -Version 7.0
<#
.SYNOPSIS
Run the repository's pinned Lean checks on Windows, with persistent local caches.
.DESCRIPTION
Use scripts/lean-lsp-check.py for repeated proof edits with persistent imports.
This wrapper provides the explicit Build and final Validate checks; see
docs/lean-local-windows.md for both workflows.
.EXAMPLE
./scripts/lean-local.ps1 Build -Targets MIPRE.Foundations.Introspection.AuxiliaryReadProgram
.EXAMPLE
./scripts/lean-local.ps1 Check -File Scratch/Example.lean -TimeoutSeconds 300
#>
[CmdletBinding()]
param(
    [Parameter(Position = 0)]
    [ValidateSet('Doctor', 'Cache', 'Build', 'Check', 'Validate')]
    [string] $Action = 'Doctor',
    [string[]] $Targets = @(),
    [string] $File,
    [ValidateRange(0, 2147483)]
    [int] $TimeoutSeconds = 0,
    [ValidateRange(1, 256)]
    [int] $Threads = 4,
    [string] $Python
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$scratchDir = Join-Path $repoRoot 'Scratch'
$configPath = Join-Path $scratchDir 'lean-local-config.json'
$logWriter = $null
$exitCode = 0
$sessionWatch = [Diagnostics.Stopwatch]::StartNew()

function Write-RunLog([string] $Text) {
    Write-Host $Text
    if ($null -ne $script:logWriter) {
        $script:logWriter.WriteLine($Text)
    }
}

function Resolve-Setting([hashtable] $Config, [string] $Key, [string] $EnvironmentName,
    [string] $Fallback) {
    $value = if ($Config.ContainsKey($Key) -and $Config[$Key]) {
        [string] $Config[$Key]
    } else {
        [Environment]::GetEnvironmentVariable($EnvironmentName, 'Process')
    }
    if ([string]::IsNullOrWhiteSpace($value)) { $value = $Fallback }
    if (-not [IO.Path]::IsPathRooted($value)) { $value = Join-Path $repoRoot $value }
    return [IO.Path]::GetFullPath($value)
}

function Stop-LoggedProcessTree([Diagnostics.Process] $Process) {
    if (-not $Process.HasExited) {
        try { $Process.Kill($true) } catch {
            # The process may exit between HasExited and Kill. Do not replace
            # its result (or timeout status) with that harmless race.
            if (-not $Process.HasExited) { throw }
        }
    }
}

function Invoke-LoggedProcess([string] $Executable, [string[]] $Arguments,
    [int] $LimitSeconds = 0) {
    # This display is for humans only. ArgumentList passes the real arguments
    # directly to the process; no shell, string evaluation, or quoting round-trip.
    $display = (@($Executable) + $Arguments | ForEach-Object {
        "'" + $_.Replace("'", "''") + "'"
    }) -join ' '
    Write-RunLog "`n[$([DateTime]::UtcNow.ToString('o'))] $display"
    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $Executable
    $startInfo.WorkingDirectory = $repoRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.StandardOutputEncoding = [Text.UTF8Encoding]::new($false)
    $startInfo.StandardErrorEncoding = [Text.UTF8Encoding]::new($false)
    foreach ($argument in $Arguments) { $startInfo.ArgumentList.Add($argument) }
    # Child-process environment only: the caller's environment needs no repair,
    # even after a failed command, timeout, or interruption.
    $startInfo.Environment['ELAN_HOME'] = $script:elanHome
    $startInfo.Environment['MATHLIB_CACHE_DIR'] = $script:mathlibCacheDir
    $startInfo.Environment['LEAN_NUM_THREADS'] = $Threads.ToString()
    $startInfo.Environment['PATH'] = $script:elanBin + [IO.Path]::PathSeparator + $env:PATH
    $startInfo.Environment['PYTHONUTF8'] = '1'
    # Lake invokes Git in freshly cloned dependencies, where this checkout's
    # local core.longpaths setting has no effect. Append a child-only setting,
    # preserving any Git environment configuration already supplied by the caller.
    $gitConfigCount = 0
    $gitConfigCountText = $startInfo.Environment['GIT_CONFIG_COUNT']
    if ($gitConfigCountText -and
        (-not [int]::TryParse($gitConfigCountText, [ref]$gitConfigCount) -or
            $gitConfigCount -lt 0 -or $gitConfigCount -eq [int]::MaxValue)) {
        throw 'GIT_CONFIG_COUNT must be a nonnegative integer below Int32.MaxValue.'
    }
    $startInfo.Environment["GIT_CONFIG_KEY_$gitConfigCount"] = 'core.longpaths'
    $startInfo.Environment["GIT_CONFIG_VALUE_$gitConfigCount"] = 'true'
    $startInfo.Environment['GIT_CONFIG_COUNT'] = ($gitConfigCount + 1).ToString()
    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    $watch = [Diagnostics.Stopwatch]::StartNew()
    $started = $false
    $timedOut = $false
    try {
        $started = $process.Start()
        $stdout = $process.StandardOutput.ReadLineAsync()
        $stderr = $process.StandardError.ReadLineAsync()
        while ($null -ne $stdout -or $null -ne $stderr -or -not $process.HasExited) {
            if (-not $timedOut -and $LimitSeconds -gt 0 -and
                $watch.Elapsed.TotalSeconds -ge $LimitSeconds) {
                $timedOut = $true
                Write-RunLog "TIMEOUT after $LimitSeconds seconds; stopping this command's process tree."
                Stop-LoggedProcessTree $process
            }
            if ($timedOut -and $watch.Elapsed.TotalSeconds -ge ($LimitSeconds + 5)) {
                # An exited parent can leave inherited pipe handles open in a
                # descendant. Bound output draining as well as process runtime.
                Write-RunLog 'Stopped waiting for redirected output after the timeout grace period.'
                break
            }
            if ($null -ne $stdout -and $stdout.IsCompleted) {
                $line = $stdout.GetAwaiter().GetResult()
                if ($null -eq $line) { $stdout = $null } else {
                    Write-RunLog $line
                    $stdout = $process.StandardOutput.ReadLineAsync()
                }
            }
            if ($null -ne $stderr -and $stderr.IsCompleted) {
                $line = $stderr.GetAwaiter().GetResult()
                if ($null -eq $line) { $stderr = $null } else {
                    Write-RunLog $line
                    $stderr = $process.StandardError.ReadLineAsync()
                }
            }
            if (($null -eq $stdout -or -not $stdout.IsCompleted) -and
                ($null -eq $stderr -or -not $stderr.IsCompleted)) {
                Start-Sleep -Milliseconds 20
            }
        }
        if (-not $process.WaitForExit(5000)) {
            $failure = [TimeoutException]::new('Command did not exit after process-tree termination.')
            $failure.Data['ExitCode'] = 124
            throw $failure
        }
        $result = if ($timedOut) { 124 } else { $process.ExitCode }
        Write-RunLog ("Exit {0}; elapsed {1:N2}s" -f $result, $watch.Elapsed.TotalSeconds)
        if ($result -ne 0) {
            $failure = [InvalidOperationException]::new("Command failed with exit code ${result}: $display")
            $failure.Data['ExitCode'] = $result
            throw $failure
        }
    } finally {
        if ($started -and -not $process.HasExited) {
            try {
                Stop-LoggedProcessTree $process
                [void] $process.WaitForExit(5000)
            } catch {
                Write-RunLog "Could not stop remaining child processes: $($_.Exception.Message)"
            }
        }
        $process.Dispose()
    }
}

function Invoke-PinnedLake([string[]] $LakeArguments, [int] $LimitSeconds = 0) {
    # Unlike an elan shim's +toolchain shorthand, run without --install refuses
    # a missing toolchain instead of downloading it during a check.
    Invoke-LoggedProcess $script:elanExe (@('run', $script:toolchain, 'lake') + $LakeArguments) $LimitSeconds
}

try {
    [void] [IO.Directory]::CreateDirectory($scratchDir)
    $logPath = Join-Path $scratchDir ("lean-local-{0}-{1}-{2}.log" -f
        [DateTime]::UtcNow.ToString('yyyyMMdd-HHmmss-fff'), $PID, $Action.ToLowerInvariant())
    $logWriter = [IO.StreamWriter]::new($logPath, $false, [Text.UTF8Encoding]::new($false))
    $logWriter.AutoFlush = $true
    $config = if (Test-Path -LiteralPath $configPath) {
        Get-Content -LiteralPath $configPath -Raw | ConvertFrom-Json -AsHashtable
    } else { @{} }
    $profileDir = [Environment]::GetFolderPath('UserProfile')
    $elanHome = Resolve-Setting $config 'elanHome' 'ELAN_HOME' (Join-Path $profileDir '.elan')
    $mathlibCacheDir = Resolve-Setting $config 'mathlibCacheDir' 'MATHLIB_CACHE_DIR' (
        Join-Path $profileDir 'MIPRECache/mathlib')
    $elanBin = Join-Path $elanHome 'bin'
    $elanExe = Join-Path $elanBin 'elan.exe'
    $toolchain = (Get-Content -LiteralPath (Join-Path $repoRoot 'lean-toolchain') -Raw).Trim()
    $manifest = Get-Content -LiteralPath (Join-Path $repoRoot 'lake-manifest.json') -Raw |
        ConvertFrom-Json
    $mathlibPin = ($manifest.packages | Where-Object name -EQ 'mathlib').rev
    Write-RunLog "Repository: $repoRoot"
    Write-RunLog "Toolchain: $toolchain"
    Write-RunLog "Mathlib: $mathlibPin"
    Write-RunLog "ELAN_HOME: $elanHome"
    Write-RunLog "MATHLIB_CACHE_DIR: $mathlibCacheDir"
    Write-RunLog "LEAN_NUM_THREADS: $Threads"
    Write-RunLog "Log: $logPath"
    if (-not (Test-Path -LiteralPath $elanExe -PathType Leaf)) {
        throw "Elan not found at $elanExe. See docs/lean-local-windows.md."
    }
    if ($Targets.Count -gt 0 -and $Action -ne 'Build') { throw '-Targets is only valid for Build.' }
    if ($File -and $Action -ne 'Check') { throw '-File is only valid for Check.' }
    foreach ($target in $Targets) {
        if ($target -notmatch '^MIPRE(?:\.[A-Za-z_][A-Za-z0-9_]*)*$') {
            throw "Use an explicit MIPRE module target (not a path or option): $target"
        }
    }
    switch ($Action) {
        'Doctor' {
            $lakeDir = Join-Path $repoRoot '.lake'
            if (Test-Path -LiteralPath $lakeDir) {
                $lakeItem = Get-Item -LiteralPath $lakeDir -Force
                Write-RunLog (".lake: {0}; target: {1}" -f $lakeItem.FullName, ($lakeItem.Target -join ', '))
            } else { Write-RunLog '.lake: missing (run the one-time setup first).' }
            $bundleInfo = Join-Path $lakeDir 'build/BUNDLE-INFO'
            if (Test-Path -LiteralPath $bundleInfo) {
                Write-RunLog "Bundle metadata (Lake still checks whether each module is current):"
                Write-RunLog (Get-Content -LiteralPath $bundleInfo -Raw)
            }
            $limit = if ($TimeoutSeconds -gt 0) { $TimeoutSeconds } else { 30 }
            Invoke-LoggedProcess $elanExe @('--version') $limit
            Invoke-LoggedProcess $elanExe @('run', $toolchain, 'lean', '--version') $limit
            Invoke-PinnedLake @('--version') $limit
            Invoke-LoggedProcess $elanExe @('run', $toolchain, 'lean', '--print-prefix') $limit
        }
        'Cache' { Invoke-PinnedLake @('exe', 'cache', 'get') $TimeoutSeconds }
        'Build' {
            $buildTargets = if ($Targets.Count -gt 0) { $Targets } else { @('MIPRE') }
            Invoke-PinnedLake (@('build') + $buildTargets) $TimeoutSeconds
        }
        'Check' {
            if (-not $File) { throw 'Check requires -File with one .lean file.' }
            $checkPath = if ([IO.Path]::IsPathRooted($File)) { $File } else { Join-Path $repoRoot $File }
            $checkPath = (Resolve-Path -LiteralPath $checkPath).Path
            if ([IO.Path]::GetExtension($checkPath) -ne '.lean') { throw 'Check requires a .lean file.' }
            $limit = if ($PSBoundParameters.ContainsKey('TimeoutSeconds')) { $TimeoutSeconds } else { 300 }
            Invoke-PinnedLake @('lean', $checkPath) $limit
        }
        'Validate' {
            if ($Python) {
                $pythonExe = (Get-Command $Python -CommandType Application -ErrorAction Stop |
                    Select-Object -First 1).Source
                $pythonArgs = @()
            } else {
                $pythonCommand = @('py.exe', 'python.exe', 'python3.exe') | ForEach-Object {
                    Get-Command $_ -CommandType Application -ErrorAction SilentlyContinue
                } | Select-Object -First 1
                if (-not $pythonCommand) { throw 'Python 3 not found; pass -Python with its executable path.' }
                $pythonExe = $pythonCommand.Source
                $pythonArgs = @(if ($pythonCommand.Name -eq 'py.exe') { '-3' })
            }
            $gitExe = (Get-Command git -CommandType Application -ErrorAction Stop |
                Select-Object -First 1).Source
            Invoke-PinnedLake @('build', 'MIPRE') $TimeoutSeconds
            Invoke-PinnedLake @('exe', 'mk_all', '--check') $TimeoutSeconds
            Invoke-LoggedProcess $pythonExe ($pythonArgs + @('scripts/lean-coverage.py', '--check')) $TimeoutSeconds
            Invoke-LoggedProcess $pythonExe ($pythonArgs + @('scripts/ledger-sync.py')) $TimeoutSeconds
            Invoke-LoggedProcess $gitExe @('-c', "safe.directory=$repoRoot", 'diff', '--check') $TimeoutSeconds
        }
    }
    Write-RunLog ("`n{0} succeeded in {1:N2}s." -f $Action, $sessionWatch.Elapsed.TotalSeconds)
} catch {
    $exitCode = if ($_.Exception.Data.Contains('ExitCode')) { [int] $_.Exception.Data['ExitCode'] } else { 1 }
    Write-RunLog "ERROR: $($_.Exception.Message)"
} finally {
    if ($null -ne $logWriter) { $logWriter.Dispose() }
}
exit $exitCode
