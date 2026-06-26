param(
    [string]$Version = $env:YULANG_VERSION,
    [string]$Prefix = $env:YULANG_INSTALL_DIR,
    [string]$Repo = $env:YULANG_INSTALL_REPO,
    [switch]$NoModifyPath
)

if ([string]::IsNullOrWhiteSpace($Version)) {
    $Version = "latest"
}
if ([string]::IsNullOrWhiteSpace($Prefix)) {
    $Prefix = Join-Path $HOME ".yulang"
}
if ([string]::IsNullOrWhiteSpace($Repo)) {
    $Repo = "momota1029/yulang"
}
$Prefix = [System.IO.Path]::GetFullPath($Prefix)

function Initialize-YulangStdCache {
    param(
        [string]$Binary,
        [string]$LibDir,
        [string]$StdRoot,
        [string]$TempDir
    )

    if ($env:YULANG_NO_SEED_CACHE -eq "1") {
        return
    }

    $seedSource = Join-Path $TempDir "std-cache-seed.yu"
    Set-Content -LiteralPath $seedSource -Encoding utf8 -Value "1"
    $previousLibDir = $env:YULANG_LIB_DIR
    try {
        $env:YULANG_LIB_DIR = $LibDir
        & $Binary --std-root $StdRoot run $seedSource *> $null
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "install.ps1: failed to seed std cache"
        }
    } finally {
        if ($null -eq $previousLibDir) {
            Remove-Item Env:YULANG_LIB_DIR -ErrorAction SilentlyContinue
        } else {
            $env:YULANG_LIB_DIR = $previousLibDir
        }
    }
}

function ConvertTo-YulangPathEntry {
    param([string]$Path)
    return [System.IO.Path]::GetFullPath($Path).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar
    )
}

function Test-YulangPathContains {
    param([string]$PathValue, [string]$Entry)
    if ([string]::IsNullOrWhiteSpace($PathValue)) {
        return $false
    }

    $entryFullName = ConvertTo-YulangPathEntry $Entry
    foreach ($part in ($PathValue -split [System.IO.Path]::PathSeparator)) {
        if ([string]::IsNullOrWhiteSpace($part)) {
            continue
        }
        $partFullName = ConvertTo-YulangPathEntry $part
        if ([string]::Equals($partFullName, $entryFullName, [System.StringComparison]::OrdinalIgnoreCase)) {
            return $true
        }
    }
    return $false
}

function Add-YulangUserPath {
    param([string]$Entry)
    if ($NoModifyPath -or $env:YULANG_NO_MODIFY_PATH -eq "1") {
        Write-Output "Skipped PATH update for $Entry"
        Write-Output "Add $Entry to PATH manually."
        return
    }

    $entryFullName = ConvertTo-YulangPathEntry $Entry
    $userPath = [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::User)
    if (Test-YulangPathContains $userPath $entryFullName) {
        if (-not (Test-YulangPathContains $env:Path $entryFullName)) {
            $env:Path = "$entryFullName$([System.IO.Path]::PathSeparator)$env:Path"
        }
        Write-Output "$entryFullName is already on the user PATH"
        return
    }

    if ([string]::IsNullOrWhiteSpace($userPath)) {
        $newUserPath = $entryFullName
    } else {
        $newUserPath = "$userPath$([System.IO.Path]::PathSeparator)$entryFullName"
    }
    [Environment]::SetEnvironmentVariable("Path", $newUserPath, [EnvironmentVariableTarget]::User)
    if (-not (Test-YulangPathContains $env:Path $entryFullName)) {
        $env:Path = "$entryFullName$([System.IO.Path]::PathSeparator)$env:Path"
    }
    Write-Output "Added $entryFullName to the user PATH"
    Write-Output "Restart your terminal to use yulang from PATH."
}

$arch = [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture
switch ($arch) {
    "X64" { $target = "x86_64-pc-windows-msvc" }
    default {
        Write-Error "install.ps1: unsupported architecture: $arch"
        exit 1
    }
}

$archive = "yulang-$target.zip"
$releaseBaseUrl = $env:YULANG_RELEASE_BASE_URL
if (-not [string]::IsNullOrWhiteSpace($releaseBaseUrl)) {
    $baseUrl = $releaseBaseUrl.TrimEnd("/")
} elseif ($Version -eq "latest") {
    $baseUrl = "https://github.com/$Repo/releases/latest/download"
} else {
    $baseUrl = "https://github.com/$Repo/releases/download/$Version"
}

$tmp = Join-Path ([System.IO.Path]::GetTempPath()) "yulang-install-$([System.Guid]::NewGuid())"
New-Item -ItemType Directory -Path $tmp | Out-Null

try {
    $archivePath = Join-Path $tmp $archive
    $sumsPath = Join-Path $tmp "SHA256SUMS"

    try {
        Invoke-WebRequest -Uri "$baseUrl/$archive" -OutFile $archivePath
    } catch {
        Write-Error "install.ps1: failed to download $archive from $baseUrl"
        if ($Version -eq "latest") {
            Write-Error "install.ps1: GitHub latest ignores prereleases; pass -Version for alpha tags"
        }
        exit 1
    }

    if ($env:YULANG_SKIP_CHECKSUM -ne "1") {
        Invoke-WebRequest -Uri "$baseUrl/SHA256SUMS" -OutFile $sumsPath
        $expectedLine = Get-Content $sumsPath | Where-Object { $_ -match "\s$([regex]::Escape($archive))$" } | Select-Object -First 1
        if ([string]::IsNullOrWhiteSpace($expectedLine)) {
            Write-Error "install.ps1: checksum entry not found for $archive"
            exit 1
        }
        $expected = ($expectedLine -split "\s+")[0]
        $actual = (Get-FileHash -Algorithm SHA256 $archivePath).Hash.ToLowerInvariant()
        if ($actual -ne $expected.ToLowerInvariant()) {
            Write-Error "install.ps1: checksum mismatch for $archive"
            Write-Error "expected: $expected"
            Write-Error "actual:   $actual"
            exit 1
        }
    }

    Expand-Archive -Path $archivePath -DestinationPath $tmp -Force
    $packageRoot = Get-ChildItem -Path $tmp -Directory -Filter "yulang-*" | Sort-Object FullName | Select-Object -First 1
    if ($null -eq $packageRoot) {
        Write-Error "install.ps1: package root not found in archive"
        exit 1
    }

    $binDir = Join-Path $Prefix "bin"
    New-Item -ItemType Directory -Path $binDir -Force | Out-Null
    $installed = Join-Path $binDir "yulang.exe"
    Copy-Item -Path (Join-Path $packageRoot.FullName "bin/yulang.exe") -Destination $installed -Force

    $libDir = Join-Path $Prefix "lib"
    New-Item -ItemType Directory -Path $libDir -Force | Out-Null
    $previousLibDir = $env:YULANG_LIB_DIR
    $stdLog = Join-Path $tmp "std-install.log"
    try {
        $env:YULANG_LIB_DIR = $libDir
        & $installed install std 2> $stdLog | Out-Null
        if ($LASTEXITCODE -ne 0) {
            if (Test-Path -LiteralPath $stdLog) {
                Get-Content -LiteralPath $stdLog | Write-Error
            }
            exit 1
        }
    } finally {
        if ($null -eq $previousLibDir) {
            Remove-Item Env:YULANG_LIB_DIR -ErrorAction SilentlyContinue
        } else {
            $env:YULANG_LIB_DIR = $previousLibDir
        }
    }
    $stdRoot = (Get-Content -LiteralPath $stdLog | Select-Object -Last 1)
    if ([string]::IsNullOrWhiteSpace($stdRoot)) {
        Write-Error "install.ps1: failed to read installed std root"
        exit 1
    }
    Initialize-YulangStdCache -Binary $installed -LibDir $libDir -StdRoot $stdRoot -TempDir $tmp

    Write-Output "Installed yulang to $installed"
    Add-YulangUserPath $binDir
} finally {
    Remove-Item -Recurse -Force $tmp -ErrorAction SilentlyContinue
}
