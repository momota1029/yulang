use std::{error::Error, fmt};

use yulang_typed_ir::{Name, Path as ModulePath};

use crate::{BandPath, RealmIdentity, RealmVersion};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalRealmPath {
    pub realm: RealmIdentity,
    pub version: Option<RealmVersion>,
    pub band: BandPath,
    pub module: ModulePath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CanonicalRealmPathParseError {
    MissingBandSeparator,
    EmptyRealm,
    EmptyBand,
    EmptyModuleSegment,
}

impl fmt::Display for CanonicalRealmPathParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingBandSeparator => write!(f, "missing `/` between realm and band"),
            Self::EmptyRealm => write!(f, "realm identity is empty"),
            Self::EmptyBand => write!(f, "band path is empty"),
            Self::EmptyModuleSegment => write!(f, "module path contains an empty segment"),
        }
    }
}

impl Error for CanonicalRealmPathParseError {}

pub fn parse_canonical_realm_path(
    input: &str,
) -> Result<CanonicalRealmPath, CanonicalRealmPathParseError> {
    let (realm_ref, band_ref) = input
        .rsplit_once('/')
        .ok_or(CanonicalRealmPathParseError::MissingBandSeparator)?;
    let (realm_identity, version) = parse_realm_ref(realm_ref)?;
    let (band, module) = parse_band_ref(band_ref)?;
    Ok(CanonicalRealmPath {
        realm: realm_identity,
        version,
        band,
        module,
    })
}

fn parse_realm_ref(
    realm_ref: &str,
) -> Result<(RealmIdentity, Option<RealmVersion>), CanonicalRealmPathParseError> {
    let trimmed = realm_ref.trim();
    if trimmed.is_empty() {
        return Err(CanonicalRealmPathParseError::EmptyRealm);
    }
    let (identity, version) = match trimmed.rsplit_once('@') {
        Some((identity, version)) if !identity.is_empty() && !version.is_empty() => {
            (identity, Some(RealmVersion(version.to_string())))
        }
        _ => (trimmed, None),
    };
    if identity.is_empty() {
        return Err(CanonicalRealmPathParseError::EmptyRealm);
    }
    Ok((RealmIdentity(identity.to_string()), version))
}

fn parse_band_ref(band_ref: &str) -> Result<(BandPath, ModulePath), CanonicalRealmPathParseError> {
    let mut segments = band_ref.split("::");
    let Some(band_segment) = segments.next().filter(|segment| !segment.is_empty()) else {
        return Err(CanonicalRealmPathParseError::EmptyBand);
    };
    let module_segments = segments
        .map(|segment| {
            if segment.is_empty() {
                return Err(CanonicalRealmPathParseError::EmptyModuleSegment);
            }
            Ok(Name(segment.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((
        BandPath::from_segments(vec![Name(band_segment.to_string())]),
        ModulePath {
            segments: module_segments,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(path: &[Name]) -> Vec<&str> {
        path.iter().map(|name| name.0.as_str()).collect()
    }

    #[test]
    fn parses_realm_version_band_and_module_path() {
        let parsed = parse_canonical_realm_path("yulang@0.1.3/std::prelude").unwrap();

        assert_eq!(parsed.realm, RealmIdentity("yulang".to_string()));
        assert_eq!(parsed.version, Some(RealmVersion("0.1.3".to_string())));
        assert_eq!(names(&parsed.band.segments), vec!["std"]);
        assert_eq!(names(&parsed.module.segments), vec!["prelude"]);
    }

    #[test]
    fn keeps_slashes_inside_realm_identity() {
        let parsed = parse_canonical_realm_path("user/program@2.0/ui::widget").unwrap();

        assert_eq!(parsed.realm, RealmIdentity("user/program".to_string()));
        assert_eq!(parsed.version, Some(RealmVersion("2.0".to_string())));
        assert_eq!(names(&parsed.band.segments), vec!["ui"]);
        assert_eq!(names(&parsed.module.segments), vec!["widget"]);
    }

    #[test]
    fn rejects_empty_module_segments() {
        let err = parse_canonical_realm_path("yulang@0.1/std::").unwrap_err();

        assert_eq!(err, CanonicalRealmPathParseError::EmptyModuleSegment);
    }
}
