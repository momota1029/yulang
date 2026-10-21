//! Exact source bytes for the R149 Yulang2 standard-library closure.

const BUNDLE: &[u8] = include_bytes!("../pinned_stdlib.bin");
const MAGIC: &[u8; 8] = b"YU2STD\0\x01";

#[derive(Clone, Debug)]
pub(crate) struct PinnedSource {
    pub(crate) path: &'static str,
    pub(crate) git_blob: [u8; 20],
    pub(crate) text: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BundleError {
    BadMagic,
    Truncated,
    InvalidUtf8,
    TrailingBytes,
}

pub(crate) fn sources() -> Result<Vec<PinnedSource>, BundleError> {
    if BUNDLE.get(..MAGIC.len()) != Some(MAGIC) {
        return Err(BundleError::BadMagic);
    }
    let mut cursor = MAGIC.len();
    let count = read_u32(&mut cursor)? as usize;
    let mut sources = Vec::with_capacity(count);
    for _ in 0..count {
        let path_len = read_u16(&mut cursor)? as usize;
        let blob_bytes = take(&mut cursor, 20)?;
        let mut git_blob = [0; 20];
        git_blob.copy_from_slice(blob_bytes);
        let text_len = read_u32(&mut cursor)? as usize;
        let path = std::str::from_utf8(take(&mut cursor, path_len)?)
            .map_err(|_| BundleError::InvalidUtf8)?;
        let text = std::str::from_utf8(take(&mut cursor, text_len)?)
            .map_err(|_| BundleError::InvalidUtf8)?;
        sources.push(PinnedSource {
            path,
            git_blob,
            text,
        });
    }
    if cursor != BUNDLE.len() {
        return Err(BundleError::TrailingBytes);
    }
    Ok(sources)
}

pub(crate) fn source_for_module(module: &str) -> Result<Option<PinnedSource>, BundleError> {
    let path = format!("lib/{}.yu", module.replace("::", "/"));
    Ok(sources()?.into_iter().find(|source| source.path == path))
}

pub(crate) fn fingerprint(blob: &[u8; 20]) -> u64 {
    u64::from_be_bytes(
        blob[..8]
            .try_into()
            .expect("Git object ID prefix is eight bytes"),
    )
}

fn take(cursor: &mut usize, length: usize) -> Result<&'static [u8], BundleError> {
    let end = cursor.checked_add(length).ok_or(BundleError::Truncated)?;
    let bytes = BUNDLE.get(*cursor..end).ok_or(BundleError::Truncated)?;
    *cursor = end;
    Ok(bytes)
}

fn read_u16(cursor: &mut usize) -> Result<u16, BundleError> {
    let bytes = take(cursor, 2)?;
    Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
}

fn read_u32(cursor: &mut usize) -> Result<u32, BundleError> {
    let bytes = take(cursor, 4)?;
    Ok(u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_bundled_source_matches_its_pinned_git_blob() {
        let sources = sources().expect("pinned source bundle parses");
        assert_eq!(sources.len(), 40);
        for source in sources {
            assert_eq!(
                git_blob_id(source.text.as_bytes()),
                source.git_blob,
                "{}",
                source.path
            );
            assert!(source.path.starts_with("lib/std/") || source.path == "lib/std.yu");
        }
    }

    #[test]
    fn module_lookup_uses_the_authentic_core_operator_source() {
        let root = source_for_module("std")
            .expect("bundle parses")
            .expect("implicit std root is pinned");
        assert_eq!(root.path, "lib/std.yu");

        let source = source_for_module("std::core::ops")
            .expect("bundle parses")
            .expect("std::core::ops is pinned");
        assert_eq!(source.path, "lib/std/core/ops.yu");
        assert!(source.text.contains("pub infix (+) 5.0.0 5.0.1"));
        assert_eq!(
            hex(&source.git_blob),
            "575e6fb15ce2d91a39004bbc7b842fedb2d83fdf"
        );
    }

    fn git_blob_id(source: &[u8]) -> [u8; 20] {
        let mut message = format!("blob {}\0", source.len()).into_bytes();
        message.extend_from_slice(source);
        sha1(&message)
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    // Small test-only SHA-1 implementation, used to verify Git's blob identity
    // without invoking Git or relying on a network-fetched hash crate.
    fn sha1(message: &[u8]) -> [u8; 20] {
        let bit_len = (message.len() as u64) * 8;
        let mut data = message.to_vec();
        data.push(0x80);
        while data.len() % 64 != 56 {
            data.push(0);
        }
        data.extend_from_slice(&bit_len.to_be_bytes());
        let mut h = [
            0x6745_2301u32,
            0xefcd_ab89,
            0x98ba_dcfe,
            0x1032_5476,
            0xc3d2_e1f0,
        ];
        for chunk in data.chunks_exact(64) {
            let mut w = [0u32; 80];
            for (i, bytes) in chunk.chunks_exact(4).enumerate() {
                w[i] = u32::from_be_bytes(bytes.try_into().expect("four-byte word"));
            }
            for i in 16..80 {
                w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
            }
            let [mut a, mut b, mut c, mut d, mut e] = h;
            for (i, word) in w.into_iter().enumerate() {
                let (f, k) = match i {
                    0..=19 => ((b & c) | (!b & d), 0x5a82_7999),
                    20..=39 => (b ^ c ^ d, 0x6ed9_eba1),
                    40..=59 => ((b & c) | (b & d) | (c & d), 0x8f1b_bcdc),
                    _ => (b ^ c ^ d, 0xca62_c1d6),
                };
                let temp = a
                    .rotate_left(5)
                    .wrapping_add(f)
                    .wrapping_add(e)
                    .wrapping_add(k)
                    .wrapping_add(word);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }
            h[0] = h[0].wrapping_add(a);
            h[1] = h[1].wrapping_add(b);
            h[2] = h[2].wrapping_add(c);
            h[3] = h[3].wrapping_add(d);
            h[4] = h[4].wrapping_add(e);
        }
        let mut result = [0; 20];
        for (chunk, word) in result.chunks_exact_mut(4).zip(h) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        result
    }
}
