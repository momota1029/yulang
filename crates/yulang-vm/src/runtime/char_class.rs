pub fn is_token_whitespace(grapheme: &str) -> bool {
    grapheme.chars().next().is_some_and(char::is_whitespace)
}

pub fn is_word_grapheme(grapheme: &str) -> bool {
    !is_token_whitespace(grapheme) && !is_token_punctuation(grapheme)
}

pub fn is_token_punctuation(grapheme: &str) -> bool {
    grapheme
        .chars()
        .next()
        .is_some_and(is_scalar_token_punctuation)
}

fn is_scalar_token_punctuation(ch: char) -> bool {
    ch.is_ascii_punctuation()
        || matches!(
            ch as u32,
            0x00A1..=0x00BF
                | 0x037E
                | 0x0387
                | 0x055A..=0x055F
                | 0x0589..=0x058A
                | 0x05BE
                | 0x05C0
                | 0x05C3
                | 0x05C6
                | 0x05F3..=0x05F4
                | 0x060C..=0x060D
                | 0x061B
                | 0x061E..=0x061F
                | 0x066A..=0x066D
                | 0x06D4
                | 0x0700..=0x070D
                | 0x07F7..=0x07F9
                | 0x0830..=0x083E
                | 0x085E
                | 0x0964..=0x0965
                | 0x0970
                | 0x09FD
                | 0x0A76
                | 0x0AF0
                | 0x0C77
                | 0x0C84
                | 0x0DF4
                | 0x0E4F
                | 0x0E5A..=0x0E5B
                | 0x0F04..=0x0F12
                | 0x0F14
                | 0x0F3A..=0x0F3D
                | 0x0F85
                | 0x0FD0..=0x0FD4
                | 0x0FD9..=0x0FDA
                | 0x104A..=0x104F
                | 0x10FB
                | 0x1360..=0x1368
                | 0x1400
                | 0x166E
                | 0x169B..=0x169C
                | 0x16EB..=0x16ED
                | 0x1735..=0x1736
                | 0x17D4..=0x17D6
                | 0x17D8..=0x17DA
                | 0x1800..=0x180A
                | 0x1944..=0x1945
                | 0x1A1E..=0x1A1F
                | 0x1AA0..=0x1AA6
                | 0x1AA8..=0x1AAD
                | 0x1B5A..=0x1B60
                | 0x1BFC..=0x1BFF
                | 0x1C3B..=0x1C3F
                | 0x1C7E..=0x1C7F
                | 0x1CC0..=0x1CC7
                | 0x1CD3
                | 0x2010..=0x2027
                | 0x2030..=0x2043
                | 0x2045..=0x2051
                | 0x2053..=0x205E
                | 0x207D..=0x207E
                | 0x208D..=0x208E
                | 0x2308..=0x230B
                | 0x2329..=0x232A
                | 0x2768..=0x2775
                | 0x27C5..=0x27C6
                | 0x27E6..=0x27EF
                | 0x2983..=0x2998
                | 0x29D8..=0x29DB
                | 0x29FC..=0x29FD
                | 0x2CF9..=0x2CFC
                | 0x2CFE..=0x2CFF
                | 0x2D70
                | 0x2E00..=0x2E5D
                | 0x3001..=0x303F
                | 0x30FB
                | 0xA4FE..=0xA4FF
                | 0xA60D..=0xA60F
                | 0xA673
                | 0xA67E
                | 0xA6F2..=0xA6F7
                | 0xA874..=0xA877
                | 0xA8CE..=0xA8CF
                | 0xA8F8..=0xA8FA
                | 0xA8FC
                | 0xA92E..=0xA92F
                | 0xA95F
                | 0xA9C1..=0xA9CD
                | 0xA9DE..=0xA9DF
                | 0xAA5C..=0xAA5F
                | 0xAADE..=0xAADF
                | 0xAAF0..=0xAAF1
                | 0xABEB
                | 0xFD3E..=0xFD3F
                | 0xFE10..=0xFE19
                | 0xFE30..=0xFE52
                | 0xFE54..=0xFE61
                | 0xFE63
                | 0xFE68
                | 0xFE6A..=0xFE6B
                | 0xFF01..=0xFF03
                | 0xFF05..=0xFF0A
                | 0xFF0C..=0xFF0F
                | 0xFF1A..=0xFF1B
                | 0xFF1F..=0xFF20
                | 0xFF3B..=0xFF3D
                | 0xFF5B..=0xFF5D
                | 0xFF5F..=0xFF65
        )
}
