use reborrow_generic::Reborrow;

#[derive(Reborrow)]
pub struct IsCut<'a> {
    pub(crate) is_root: bool,
    pub(crate) is_cut: &'a mut bool,
}

impl<'a> IsCut<'a> {
    pub fn new(is_cut: &'a mut bool) -> Self {
        Self {
            is_root: true,
            is_cut,
        }
    }

    pub fn non_root(is_cut: &'a mut bool) -> Self {
        Self {
            is_root: false,
            is_cut,
        }
    }

    pub fn cut(&mut self) {
        *self.is_cut = true;
    }

    pub fn capture_cut<O>(&mut self, f: impl FnOnce(IsCut) -> O) -> (O, bool) {
        if *self.is_cut {
            let mut is_consumed = false;
            return (f(IsCut::non_root(&mut is_consumed)), is_consumed);
        }
        let out = f(IsCut {
            is_root: self.is_root,
            is_cut: self.is_cut,
        });
        (out, *self.is_cut)
    }
}
