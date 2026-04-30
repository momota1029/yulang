use darling::{FromDeriveInput, FromField, FromVariant};
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    DeriveInput, Lifetime, Type, TypePath, parse_macro_input,
    visit_mut::{self, VisitMut},
};

#[derive(FromDeriveInput)]
#[darling(attributes(reborrow), supports(struct_any, enum_any))]
struct ReborrowInput {
    ident: syn::Ident,
    generics: syn::Generics,
    data: darling::ast::Data<ReborrowVariant, ReborrowField>,

    #[darling(default)]
    lifetime: Option<String>,

    #[darling(default)]
    lifetimes: Option<String>,

    #[darling(default, rename = "ref")]
    ref_mode: bool,
}

#[derive(FromVariant)]
#[darling(attributes(reborrow))]
struct ReborrowVariant {
    ident: syn::Ident,
    fields: darling::ast::Fields<ReborrowField>,
}

#[derive(FromField)]
#[darling(attributes(reborrow))]
struct ReborrowField {
    ident: Option<syn::Ident>,
    ty: syn::Type,

    #[darling(default)]
    clone: bool,

    #[darling(default, rename = "type")]
    type_hint: Option<String>,
}

enum FieldKind {
    Normal { long_type: Type },
    Clone,
    Target { base_type: Type, long_type: Type },
}

#[derive(Copy, Clone)]
enum FieldMethod {
    Rb,
    Shorten,
    ShortenMut,
}

#[proc_macro_derive(Reborrow, attributes(reborrow))]
pub fn derive_reborrow(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let input = ReborrowInput::from_derive_input(&input).unwrap();

    if input.ref_mode {
        let expanded = impl_ref_reborrow(&input.ident, &input.generics);
        return TokenStream::from(expanded);
    }

    let target_lifetimes = parse_lifetimes(&input);
    let expanded = match &input.data {
        darling::ast::Data::Struct(fields) => {
            impl_struct(&input.ident, &input.generics, fields, &target_lifetimes)
        }
        darling::ast::Data::Enum(variants) => {
            impl_enum(&input.ident, &input.generics, variants, &target_lifetimes)
        }
    };

    TokenStream::from(expanded)
}

fn impl_ref_reborrow(name: &syn::Ident, generics: &syn::Generics) -> proc_macro2::TokenStream {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let short_type = quote! { &'short mut #name #ty_generics };
    let long_type = quote! { &'long mut #name #ty_generics };

    quote! {
        impl #impl_generics ::reborrow_generic::Reborrow for #name #ty_generics #where_clause {
            type Target<'short> = #short_type where Self: 'short;

            fn rb<'short>(&'short mut self) -> #short_type {
                self
            }

            fn shorten<'short, 'long: 'short>(
                this: #long_type
            ) -> #short_type {
                this
            }

            fn shorten_mut<'short, 'long>(
                this: &'short mut #long_type
            ) -> #short_type {
                *this
            }
        }
    }
}

fn parse_lifetimes(input: &ReborrowInput) -> Vec<String> {
    if let Some(ref lts) = input.lifetimes {
        lts.split(',')
            .map(|s| s.trim().trim_start_matches("'").to_string())
            .collect()
    } else if let Some(ref lt) = input.lifetime {
        vec![lt.trim().trim_start_matches("'").to_string()]
    } else {
        input
            .generics
            .params
            .iter()
            .find_map(|p| match p {
                syn::GenericParam::Lifetime(lt) => Some(lt.lifetime.ident.to_string()),
                _ => None,
            })
            .into_iter()
            .collect()
    }
}

impl ReborrowField {
    fn kind(&self, target_lifetimes: &[String]) -> FieldKind {
        if self.clone {
            return FieldKind::Clone;
        }

        if let Some(ref hint) = self.type_hint {
            let base_type: syn::Type = syn::parse_str(hint).unwrap();
            let long_type = substitute_type_lifetimes(&base_type, target_lifetimes, "'long");
            return FieldKind::Target {
                base_type,
                long_type,
            };
        }

        if let Some(base_type) = detect_target_type(&self.ty) {
            let long_type = substitute_type_lifetimes(&base_type, target_lifetimes, "'long");
            return FieldKind::Target {
                base_type,
                long_type,
            };
        }

        let long_type = substitute_type_lifetimes(&self.ty, target_lifetimes, "'long");
        FieldKind::Normal { long_type }
    }
}

fn detect_target_type(ty: &Type) -> Option<Type> {
    let Type::Path(tp) = ty else { return None };

    // 最終セグメントが "Target" でなければ関与しない
    let last = tp.path.segments.last()?;
    if last.ident != "Target" {
        return None;
    }

    // <T as Trait>::Target / <T>::Target / T::Target（qself あり）なら Self 側を返す
    if let Some(q) = &tp.qself {
        return Some((*q.ty).clone());
    }

    // 通常のパス T::Target のときは末尾セグメントを落としてから末尾の区切りも落とす
    if tp.path.segments.len() >= 2 {
        let mut base_path = tp.path.clone();
        base_path.segments.pop(); // drop "Target"
        if base_path.segments.trailing_punct() {
            base_path.segments.pop_punct(); // drop trailing "::"
        }
        return Some(Type::Path(TypePath {
            qself: None,
            path: base_path,
        }));
    }

    None
}

struct LifetimeSubstituter {
    target_lifetimes: Vec<String>,
    replacement: syn::Lifetime,
}

impl VisitMut for LifetimeSubstituter {
    fn visit_lifetime_mut(&mut self, lifetime: &mut syn::Lifetime) {
        if self.target_lifetimes.contains(&lifetime.ident.to_string()) {
            *lifetime = self.replacement.clone();
        }
        visit_mut::visit_lifetime_mut(self, lifetime);
    }
}

fn substitute_type_lifetimes(ty: &Type, target_lifetimes: &[String], replacement: &str) -> Type {
    let mut ty = ty.clone();
    let mut substituter = LifetimeSubstituter {
        target_lifetimes: target_lifetimes.to_vec(),
        replacement: syn::parse_str(replacement).unwrap(),
    };
    substituter.visit_type_mut(&mut ty);
    ty
}

fn generate_field_expr(
    field_access: proc_macro2::TokenStream,
    kind: &FieldKind,
    method: FieldMethod,
    is_already_mut: bool,
) -> proc_macro2::TokenStream {
    match (kind, method) {
        (FieldKind::Clone, _) => {
            quote! { #field_access.clone() }
        }
        (FieldKind::Target { base_type, .. }, FieldMethod::Rb) if !is_already_mut => {
            quote! { <#base_type as ::reborrow_generic::Reborrow>::shorten_mut(&mut #field_access) }
        }
        (FieldKind::Target { base_type, .. }, FieldMethod::Rb) => {
            quote! { <#base_type as ::reborrow_generic::Reborrow>::shorten_mut(#field_access) }
        }
        (FieldKind::Target { long_type, .. }, FieldMethod::Shorten) => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten(#field_access) }
        }
        (FieldKind::Target { long_type, .. }, FieldMethod::ShortenMut) if !is_already_mut => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten_mut(&mut #field_access) }
        }
        (FieldKind::Target { long_type, .. }, FieldMethod::ShortenMut) => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten_mut(#field_access) }
        }
        (FieldKind::Normal { .. }, FieldMethod::Rb) if !is_already_mut => {
            quote! { ::reborrow_generic::Reborrow::rb(&mut #field_access) }
        }
        (FieldKind::Normal { .. }, FieldMethod::Rb) => {
            quote! { ::reborrow_generic::Reborrow::rb(#field_access) }
        }
        (FieldKind::Normal { long_type, .. }, FieldMethod::Shorten) => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten(#field_access) }
        }
        (FieldKind::Normal { long_type, .. }, FieldMethod::ShortenMut) if !is_already_mut => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten_mut(&mut #field_access) }
        }
        (FieldKind::Normal { long_type, .. }, FieldMethod::ShortenMut) => {
            quote! { <#long_type as ::reborrow_generic::Reborrow>::shorten_mut(#field_access) }
        }
    }
}

fn build_target_type(
    name: &syn::Ident,
    generics: &syn::Generics,
    target_lifetimes: &[String],
    replacement: &str,
) -> proc_macro2::TokenStream {
    let params = generics.params.iter().map(|param| match param {
        syn::GenericParam::Lifetime(lt)
            if target_lifetimes.contains(&lt.lifetime.ident.to_string()) =>
        {
            let lifetime: Lifetime = syn::parse_str(replacement).unwrap();
            quote! { #lifetime }
        }
        syn::GenericParam::Lifetime(lt) => {
            let lifetime = &lt.lifetime;
            quote! { #lifetime }
        }
        syn::GenericParam::Type(ty) => {
            let ident = &ty.ident;
            quote! { #ident }
        }
        syn::GenericParam::Const(c) => {
            let ident = &c.ident;
            quote! { #ident }
        }
    });

    if generics.params.is_empty() {
        quote! { #name }
    } else {
        quote! { #name<#(#params),*> }
    }
}

fn impl_struct(
    name: &syn::Ident,
    generics: &syn::Generics,
    fields: &darling::ast::Fields<ReborrowField>,
    target_lifetimes: &[String],
) -> proc_macro2::TokenStream {
    let target_short_type = build_target_type(name, generics, target_lifetimes, "'short");
    let target_long_type = build_target_type(name, generics, target_lifetimes, "'long");
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    match fields.style {
        darling::ast::Style::Struct => {
            let field_exprs_rb = fields.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let expr = generate_field_expr(
                    quote! { self.#field_name },
                    &f.kind(target_lifetimes),
                    FieldMethod::Rb,
                    false,
                );
                quote! { #field_name: #expr }
            });

            let field_exprs_shorten = fields.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let expr = generate_field_expr(
                    quote! { this.#field_name },
                    &f.kind(target_lifetimes),
                    FieldMethod::Shorten,
                    false,
                );
                quote! { #field_name: #expr }
            });

            let field_exprs_shorten_mut = fields.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let expr = generate_field_expr(
                    quote! { this.#field_name },
                    &f.kind(target_lifetimes),
                    FieldMethod::ShortenMut,
                    false,
                );
                quote! { #field_name: #expr }
            });

            quote! {
                impl #impl_generics ::reborrow_generic::Reborrow for #name #ty_generics #where_clause {
                    type Target<'short> = #target_short_type where Self: 'short;

                    fn rb<'short>(&'short mut self) -> #target_short_type {
                        #name { #(#field_exprs_rb,)* }
                    }

                    fn shorten<'short, 'long: 'short>(
                        this: #target_long_type
                    ) -> #target_short_type {
                        #name { #(#field_exprs_shorten,)* }
                    }

                    fn shorten_mut<'short, 'long>(
                        this: &'short mut #target_long_type
                    ) -> #target_short_type {
                        #name { #(#field_exprs_shorten_mut,)* }
                    }
                }
            }
        }
        darling::ast::Style::Tuple => {
            let field_exprs_rb = fields.iter().enumerate().map(|(i, f)| {
                let index = syn::Index::from(i);
                generate_field_expr(
                    quote! { self.#index },
                    &f.kind(target_lifetimes),
                    FieldMethod::Rb,
                    false,
                )
            });

            let field_exprs_shorten = fields.iter().enumerate().map(|(i, f)| {
                let index = syn::Index::from(i);
                generate_field_expr(
                    quote! { this.#index },
                    &f.kind(target_lifetimes),
                    FieldMethod::Shorten,
                    false,
                )
            });

            let field_exprs_shorten_mut = fields.iter().enumerate().map(|(i, f)| {
                let index = syn::Index::from(i);
                generate_field_expr(
                    quote! { this.#index },
                    &f.kind(target_lifetimes),
                    FieldMethod::ShortenMut,
                    false,
                )
            });

            quote! {
                impl #impl_generics ::reborrow_generic::Reborrow for #name #ty_generics #where_clause {
                    type Target<'short> = #target_short_type where Self: 'short;

                    fn rb<'short>(&'short mut self) -> #target_short_type {
                        #name(#(#field_exprs_rb,)*)
                    }

                    fn shorten<'short, 'long: 'short>(
                        this: #target_long_type
                    ) -> #target_short_type {
                        #name(#(#field_exprs_shorten,)*)
                    }

                    fn shorten_mut<'short, 'long>(
                        this: &'short mut #target_long_type
                    ) -> #target_short_type {
                        #name(#(#field_exprs_shorten_mut,)*)
                    }
                }
            }
        }
        darling::ast::Style::Unit => {
            quote! {
                impl #impl_generics ::reborrow_generic::Reborrow for #name #ty_generics #where_clause {
                    type Target<'short> = #target_short_type where Self: 'short;

                    fn rb<'short>(&'short mut self) -> #target_short_type {
                        #name
                    }

                    fn shorten<'short, 'long: 'short>(
                        this: #target_long_type
                    ) -> #target_short_type {
                        #name
                    }

                    fn shorten_mut<'short, 'long>(
                        this: &'short mut #target_long_type
                    ) -> #target_short_type {
                        #name
                    }
                }
            }
        }
    }
}

fn impl_enum(
    name: &syn::Ident,
    generics: &syn::Generics,
    variants: &[ReborrowVariant],
    target_lifetimes: &[String],
) -> proc_macro2::TokenStream {
    let target_short_type = build_target_type(name, generics, target_lifetimes, "'short");
    let target_long_type = build_target_type(name, generics, target_lifetimes, "'long");
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let rb_arms = variants
        .iter()
        .map(|variant| generate_variant_arm(name, variant, FieldMethod::Rb, target_lifetimes));

    let shorten_arms = variants
        .iter()
        .map(|variant| generate_variant_arm(name, variant, FieldMethod::Shorten, target_lifetimes));

    let shorten_mut_arms = variants.iter().map(|variant| {
        generate_variant_arm(name, variant, FieldMethod::ShortenMut, target_lifetimes)
    });

    quote! {
        impl #impl_generics ::reborrow_generic::Reborrow for #name #ty_generics #where_clause {
            type Target<'short> = #target_short_type where Self: 'short;

            fn rb<'short>(&'short mut self) -> #target_short_type {
                match self {
                    #(#rb_arms,)*
                }
            }

            fn shorten<'short, 'long: 'short>(
                this: #target_long_type
            ) -> #target_short_type {
                match this {
                    #(#shorten_arms,)*
                }
            }

            fn shorten_mut<'short, 'long>(
                this: &'short mut #target_long_type
            ) -> #target_short_type {
                match this {
                    #(#shorten_mut_arms,)*
                }
            }
        }
    }
}

fn generate_variant_arm(
    enum_name: &syn::Ident,
    variant: &ReborrowVariant,
    method: FieldMethod,
    target_lifetimes: &[String],
) -> proc_macro2::TokenStream {
    let variant_name = &variant.ident;

    match variant.fields.style {
        darling::ast::Style::Struct => {
            let field_names: Vec<_> = variant
                .fields
                .iter()
                .map(|f| f.ident.as_ref().unwrap())
                .collect();
            let field_exprs = variant.fields.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let expr = generate_field_expr(
                    quote! { #field_name },
                    &f.kind(target_lifetimes),
                    method,
                    true,
                );
                quote! { #field_name: #expr }
            });
            quote! {
                #enum_name::#variant_name { #(#field_names,)* } => {
                    #enum_name::#variant_name { #(#field_exprs,)* }
                }
            }
        }
        darling::ast::Style::Tuple => {
            let bindings: Vec<_> = (0..variant.fields.len())
                .map(|i| quote::format_ident!("f{}", i))
                .collect();
            let field_exprs = variant.fields.iter().zip(&bindings).map(|(f, binding)| {
                generate_field_expr(quote! { #binding }, &f.kind(target_lifetimes), method, true)
            });
            quote! {
                #enum_name::#variant_name(#(#bindings,)*) => {
                    #enum_name::#variant_name(#(#field_exprs,)*)
                }
            }
        }
        darling::ast::Style::Unit => {
            quote! {
                #enum_name::#variant_name => #enum_name::#variant_name
            }
        }
    }
}
