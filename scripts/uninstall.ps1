param(
    [string]$Prefix = $env:YULANG_INSTALL_DIR,
    [switch]$All,
    [switch]$PurgeCache,
    [switch]$NoModifyPath
)

if ([string]::IsNullOrWhiteSpace($Prefix)) {
    $Prefix = Join-Path $HOME ".yulang"
}
if ([string]::IsNullOrWhiteSpace($Prefix)) {
    Write-Error "uninstall.ps1: empty prefix"
    exit 1
}

function Get-YulangCanonicalPath {
    param([string]$Path)
    if (Test-Path -LiteralPath $Path) {
        return [System.IO.Path]::GetFullPath((Resolve-Path -LiteralPath $Path).ProviderPath)
    }
    return [System.IO.Path]::GetFullPath($Path)
}

function Test-YulangSamePath {
    param([string]$Left, [string]$Right)
    return [string]::Equals(
        $Left.TrimEnd([System.IO.Path]::DirectorySeparatorChar, [System.IO.Path]::AltDirectorySeparatorChar),
        $Right.TrimEnd([System.IO.Path]::DirectorySeparatorChar, [System.IO.Path]::AltDirectorySeparatorChar),
        [System.StringComparison]::OrdinalIgnoreCase
    )
}

function ConvertTo-YulangPathEntry {
    param([string]$Path)
    return [System.IO.Path]::GetFullPath($Path).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar
    )
}

function Remove-YulangUserPath {
    param([string]$Entry)
    if ($NoModifyPath -or $env:YULANG_NO_MODIFY_PATH -eq "1") {
        return
    }

    $entryFullName = ConvertTo-YulangPathEntry $Entry
    $userPath = [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::User)
    if ([string]::IsNullOrWhiteSpace($userPath)) {
        return
    }

    $kept = @()
    $removed = $false
    foreach ($part in ($userPath -split [System.IO.Path]::PathSeparator)) {
        if ([string]::IsNullOrWhiteSpace($part)) {
            continue
        }
        $partFullName = ConvertTo-YulangPathEntry $part
        if ([string]::Equals($partFullName, $entryFullName, [System.StringComparison]::OrdinalIgnoreCase)) {
            $removed = $true
            continue
        }
        $kept += $part
    }

    if ($removed) {
        [Environment]::SetEnvironmentVariable("Path", ($kept -join [System.IO.Path]::PathSeparator), [EnvironmentVariableTarget]::User)
        Write-Output "Removed $entryFullName from the user PATH"
    }
}

$homeFullName = Get-YulangCanonicalPath $HOME
$prefixFullName = Get-YulangCanonicalPath $Prefix
if ((Test-YulangSamePath $prefixFullName ([System.IO.Path]::GetPathRoot($prefixFullName))) -or (Test-YulangSamePath $prefixFullName $homeFullName)) {
    Write-Error "uninstall.ps1: refusing to remove unsafe prefix: $Prefix"
    exit 1
}

function Remove-YulangPath {
    param([string]$Path)
    if (Test-Path -LiteralPath $Path) {
        Remove-Item -LiteralPath $Path -Recurse -Force
        Write-Output "Removed $Path"
    }
}

function Remove-EmptyDir {
    param([string]$Path)
    if ((Test-Path -LiteralPath $Path) -and -not (Get-ChildItem -LiteralPath $Path -Force | Select-Object -First 1)) {
        Remove-Item -LiteralPath $Path -Force
    }
}

function Get-YulangCacheRoot {
    if (-not [string]::IsNullOrWhiteSpace($env:YULANG_CACHE_DIR)) {
        return $env:YULANG_CACHE_DIR
    }
    if (-not [string]::IsNullOrWhiteSpace($env:XDG_CACHE_HOME)) {
        return (Join-Path $env:XDG_CACHE_HOME "yulang")
    }
    return (Join-Path (Join-Path $HOME ".cache") "yulang")
}

if ($All) {
    Remove-YulangPath $Prefix
} else {
    $binDir = Join-Path $Prefix "bin"
    Remove-YulangPath (Join-Path $binDir "yulang")
    Remove-YulangPath (Join-Path $binDir "yulang.exe")
    Remove-YulangPath (Join-Path $binDir "yulang-lsp")
    Remove-YulangPath (Join-Path $binDir "yulang-lsp.exe")

    $libDir = Join-Path $Prefix "lib"
    if (Test-Path -LiteralPath $libDir) {
        Get-ChildItem -LiteralPath $libDir -Directory -Filter "yulang-*" |
            ForEach-Object { Remove-YulangPath $_.FullName }
    }

    Remove-EmptyDir $binDir
    Remove-EmptyDir $libDir
    Remove-EmptyDir $Prefix
}

if ($PurgeCache) {
    Remove-YulangPath (Get-YulangCacheRoot)
}

Write-Output "Uninstalled yulang from $Prefix"
$pathEntry = Join-Path $Prefix "bin"
Remove-YulangUserPath $pathEntry
