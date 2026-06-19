param(
    [Parameter(Mandatory = $true)]
    [string]$Archive
)

$ErrorActionPreference = "Stop"

if (-not (Test-Path -LiteralPath $Archive)) {
    Write-Error "release install smoke: archive not found: $Archive"
    exit 1
}
if (-not $Archive.EndsWith(".zip", [System.StringComparison]::OrdinalIgnoreCase)) {
    Write-Error "release install smoke: install.ps1 expects a Windows zip archive"
    exit 1
}

$repoRoot = Split-Path -Parent $PSScriptRoot
$distDir = (Resolve-Path -LiteralPath (Split-Path -Parent $Archive)).ProviderPath
$archiveName = Split-Path -Leaf $Archive

foreach ($name in @("install.sh", "install.ps1", "uninstall.sh", "uninstall.ps1")) {
    $target = Join-Path $distDir $name
    Copy-Item -LiteralPath (Join-Path $PSScriptRoot $name) -Destination $target -Force
}

$sumsPath = Join-Path $distDir "SHA256SUMS"
$lines = foreach ($name in @($archiveName, "install.sh", "install.ps1", "uninstall.sh", "uninstall.ps1")) {
    $hash = (Get-FileHash -Algorithm SHA256 (Join-Path $distDir $name)).Hash.ToLowerInvariant()
    "$hash  $name"
}
Set-Content -LiteralPath $sumsPath -Value $lines -Encoding utf8

$tmp = Join-Path ([System.IO.Path]::GetTempPath()) "yulang-release-install-smoke-$([System.Guid]::NewGuid())"
New-Item -ItemType Directory -Path $tmp | Out-Null
$prefix = Join-Path $tmp "prefix"
$home = Join-Path $tmp "home"
$cache = Join-Path $tmp "cache"
$main = Join-Path $tmp "main.yu"
New-Item -ItemType Directory -Path $home, $cache | Out-Null

$releaseServerProcess = $null
$previousHome = $env:HOME
$previousUserProfile = $env:USERPROFILE
$previousCache = $env:YULANG_CACHE_DIR
$previousStd = $env:YULANG_STD
$previousLib = $env:YULANG_LIB_DIR
$previousBase = $env:YULANG_RELEASE_BASE_URL
$previousUserPath = [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::User)

$pythonCommand = Get-Command python3 -ErrorAction SilentlyContinue
if ($null -eq $pythonCommand) {
    $pythonCommand = Get-Command python -ErrorAction SilentlyContinue
}
if ($null -eq $pythonCommand) {
    Write-Error "release install smoke: python3 or python is required"
    exit 1
}
$powerShellCommand = (Get-Process -Id $PID).Path

function Start-ReleaseServer {
    param([string]$Root)
    $serverScript = Join-Path $tmp "release-server.py"
    $portFile = Join-Path $tmp "release-server.port"
    Set-Content -LiteralPath $serverScript -Encoding utf8 -Value @'
import functools
import http.server
import pathlib
import socketserver
import sys

dist = pathlib.Path(sys.argv[1])
port_file = pathlib.Path(sys.argv[2])

class Handler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

handler = functools.partial(Handler, directory=str(dist))

class Server(socketserver.TCPServer):
    allow_reuse_address = True

with Server(("127.0.0.1", 0), handler) as httpd:
    port_file.write_text(str(httpd.server_address[1]), encoding="utf-8")
    httpd.serve_forever()
'@
    $stdout = Join-Path $tmp "release-server.out"
    $stderr = Join-Path $tmp "release-server.err"
    $process = Start-Process -FilePath $pythonCommand.Source -ArgumentList @($serverScript, $Root, $portFile) -PassThru -WindowStyle Hidden -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    for ($i = 0; $i -lt 100; $i++) {
        if (Test-Path -LiteralPath $portFile) {
            $port = (Get-Content -LiteralPath $portFile -Raw).Trim()
            if (-not [string]::IsNullOrWhiteSpace($port)) {
                return @("http://127.0.0.1:$port", $process)
            }
        }
        if ($process.HasExited) {
            break
        }
        Start-Sleep -Milliseconds 50
    }
    if ($process.HasExited) {
        if (Test-Path -LiteralPath $stderr) {
            Get-Content -LiteralPath $stderr | Write-Error
        }
    }
    throw "release install smoke: local release server did not start"
}

function Install-Yulang {
    & (Join-Path $PSScriptRoot "install.ps1") -Version "smoke" -Prefix $prefix | Out-Null
    $bin = Join-Path $prefix "bin/yulang.exe"
    if (-not (Test-Path -LiteralPath $bin)) {
        throw "release install smoke: installed yulang.exe not found"
    }
    if (-not (Get-ChildItem -LiteralPath (Join-Path $prefix "lib") -Directory -Filter "yulang-*" | Where-Object { Test-Path -LiteralPath (Join-Path $_.FullName "std.yu") } | Select-Object -First 1)) {
        throw "release install smoke: versioned std root not installed under prefix"
    }
    Assert-PathRegistered
}

function Assert-NoHomeStd {
    $homeLib = Join-Path $home ".yulang/lib"
    if ((Test-Path -LiteralPath $homeLib) -and (Get-ChildItem -LiteralPath $homeLib -Directory -Filter "yulang-*" | Select-Object -First 1)) {
        throw "release install smoke: runtime created std under HOME instead of install prefix"
    }
}

function ConvertTo-SmokePathEntry {
    param([string]$Path)
    return [System.IO.Path]::GetFullPath($Path).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar
    )
}

function Test-SmokeUserPathContains {
    param([string]$Entry)
    $entryFullName = ConvertTo-SmokePathEntry $Entry
    $userPath = [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::User)
    if ([string]::IsNullOrWhiteSpace($userPath)) {
        return $false
    }

    foreach ($part in ($userPath -split [System.IO.Path]::PathSeparator)) {
        if ([string]::IsNullOrWhiteSpace($part)) {
            continue
        }
        $partFullName = ConvertTo-SmokePathEntry $part
        if ([string]::Equals($partFullName, $entryFullName, [System.StringComparison]::OrdinalIgnoreCase)) {
            return $true
        }
    }
    return $false
}

function Assert-PathRegistered {
    $entry = Join-Path $prefix "bin"
    if (-not (Test-SmokeUserPathContains $entry)) {
        throw "release install smoke: installer did not add $entry to the user PATH"
    }
}

function Assert-PathRemoved {
    $entry = Join-Path $prefix "bin"
    if (Test-SmokeUserPathContains $entry) {
        throw "release install smoke: uninstaller left $entry in the user PATH"
    }
}

try {
    $server = Start-ReleaseServer -Root $distDir
    $env:YULANG_RELEASE_BASE_URL = $server[0]
    $releaseServerProcess = $server[1]

    $env:HOME = $home
    $env:USERPROFILE = $home
    $env:YULANG_CACHE_DIR = $cache
    Remove-Item Env:YULANG_STD -ErrorAction SilentlyContinue
    Remove-Item Env:YULANG_LIB_DIR -ErrorAction SilentlyContinue

    Set-Content -LiteralPath $main -Encoding utf8 -Value @'
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once.show
'@

    Install-Yulang
    $bin = Join-Path $prefix "bin/yulang.exe"
    & $bin check $main | Out-Null
    $runOutput = & $bin run --print-roots $main
    if ($runOutput -notmatch '"just \(3, 4, 5\)"') {
        throw "release install smoke: unexpected run output: $runOutput"
    }
    Assert-NoHomeStd

    $serverProcess = Start-Process -FilePath $bin -ArgumentList @("server") -PassThru -NoNewWindow -RedirectStandardOutput (Join-Path $tmp "server.out") -RedirectStandardError (Join-Path $tmp "server.err")
    Start-Sleep -Seconds 2
    if ($serverProcess.HasExited -and $serverProcess.ExitCode -ne 0) {
        throw "release install smoke: yulang server failed to start, status $($serverProcess.ExitCode)"
    }
    if (-not $serverProcess.HasExited) {
        Stop-Process -Id $serverProcess.Id -Force
        $serverProcess.WaitForExit()
    }

    New-Item -ItemType File -Path (Join-Path $prefix "sentinel") -Force | Out-Null
    New-Item -ItemType File -Path (Join-Path $cache "sentinel") -Force | Out-Null
    & (Join-Path $PSScriptRoot "uninstall.ps1") -Prefix $prefix | Out-Null
    if (Test-Path -LiteralPath $bin) {
        throw "release install smoke: default uninstall left yulang.exe"
    }
    if (-not (Test-Path -LiteralPath (Join-Path $prefix "sentinel"))) {
        throw "release install smoke: default uninstall removed prefix sentinel"
    }
    if (-not (Test-Path -LiteralPath (Join-Path $cache "sentinel"))) {
        throw "release install smoke: default uninstall removed cache sentinel"
    }
    Assert-PathRemoved

    Install-Yulang
    New-Item -ItemType Directory -Path $cache -Force | Out-Null
    New-Item -ItemType File -Path (Join-Path $cache "sentinel") -Force | Out-Null
    & (Join-Path $PSScriptRoot "uninstall.ps1") -Prefix $prefix -PurgeCache | Out-Null
    if (Test-Path -LiteralPath $cache) {
        throw "release install smoke: purge-cache left cache root"
    }
    Assert-PathRemoved

    Install-Yulang
    New-Item -ItemType File -Path (Join-Path $prefix "sentinel") -Force | Out-Null
    & (Join-Path $PSScriptRoot "uninstall.ps1") -Prefix $prefix -All | Out-Null
    if (Test-Path -LiteralPath $prefix) {
        throw "release install smoke: all uninstall left prefix"
    }
    Assert-PathRemoved

    New-Item -ItemType File -Path (Join-Path $home "sentinel") -Force | Out-Null
    $unsafe = Start-Process -FilePath $powerShellCommand -ArgumentList @("-NoProfile", "-File", (Join-Path $PSScriptRoot "uninstall.ps1"), "-Prefix", (Join-Path $home "."), "-All") -PassThru -Wait -NoNewWindow -RedirectStandardOutput (Join-Path $tmp "unsafe.out") -RedirectStandardError (Join-Path $tmp "unsafe.err")
    if ($unsafe.ExitCode -eq 0 -or -not (Test-Path -LiteralPath (Join-Path $home "sentinel"))) {
        throw "release install smoke: unsafe prefix was not rejected"
    }

    Write-Output "release install smoke ok: $archiveName"
} finally {
    if ($null -ne $releaseServerProcess -and -not $releaseServerProcess.HasExited) {
        Stop-Process -Id $releaseServerProcess.Id -Force -ErrorAction SilentlyContinue
        $releaseServerProcess.WaitForExit()
    }
    if ($null -eq $previousHome) { Remove-Item Env:HOME -ErrorAction SilentlyContinue } else { $env:HOME = $previousHome }
    if ($null -eq $previousUserProfile) { Remove-Item Env:USERPROFILE -ErrorAction SilentlyContinue } else { $env:USERPROFILE = $previousUserProfile }
    if ($null -eq $previousCache) { Remove-Item Env:YULANG_CACHE_DIR -ErrorAction SilentlyContinue } else { $env:YULANG_CACHE_DIR = $previousCache }
    if ($null -eq $previousStd) { Remove-Item Env:YULANG_STD -ErrorAction SilentlyContinue } else { $env:YULANG_STD = $previousStd }
    if ($null -eq $previousLib) { Remove-Item Env:YULANG_LIB_DIR -ErrorAction SilentlyContinue } else { $env:YULANG_LIB_DIR = $previousLib }
    if ($null -eq $previousBase) { Remove-Item Env:YULANG_RELEASE_BASE_URL -ErrorAction SilentlyContinue } else { $env:YULANG_RELEASE_BASE_URL = $previousBase }
    [Environment]::SetEnvironmentVariable("Path", $previousUserPath, [EnvironmentVariableTarget]::User)
    Remove-Item -Recurse -Force $tmp -ErrorAction SilentlyContinue
}
