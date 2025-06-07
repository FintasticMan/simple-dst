use quote::{IdentFragment, ToTokens, format_ident, quote};
use syn::{
    Attribute, Data, DataStruct, DeriveInput, Error, Fields, FieldsNamed, FieldsUnnamed, Ident,
    Index, Path, Token, Type, Visibility, parse::ParseStream, parse_macro_input, parse_quote,
};

fn is_repr_c(attrs: &[Attribute]) -> bool {
    mod kw {
        syn::custom_keyword!(C);
    }
    attrs
        .iter()
        .any(|a| a.path().is_ident("repr") && a.parse_args::<kw::C>().is_ok())
}

enum FieldIdent {
    Ident(Ident),
    Index(Index),
}

impl IdentFragment for FieldIdent {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::Ident(ident) => ident.fmt(f),
            Self::Index(index) => index.fmt(f),
        }
    }

    fn span(&self) -> Option<proc_macro2::Span> {
        match self {
            Self::Ident(ident) => IdentFragment::span(ident),
            Self::Index(index) => IdentFragment::span(index),
        }
    }
}

impl ToTokens for FieldIdent {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Ident(ident) => ident.to_tokens(tokens),
            Self::Index(index) => index.to_tokens(tokens),
        }
    }
}

struct Field {
    ident: FieldIdent,
    ty: Type,
}

fn get_fields(data: &Data) -> Vec<Field> {
    match data {
        Data::Struct(DataStruct { fields, .. }) => match fields {
            Fields::Named(FieldsNamed { named, .. }) => named
                .iter()
                .map(|f| Field {
                    ident: FieldIdent::Ident(f.ident.as_ref().unwrap().clone()),
                    ty: f.ty.clone(),
                })
                .collect(),
            Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => unnamed
                .iter()
                .enumerate()
                .map(|(i, f)| Field {
                    ident: FieldIdent::Index(i.into()),
                    ty: f.ty.clone(),
                })
                .collect(),
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
    }
}

struct DstAttrs {
    simple_dst_crate: Option<Path>,
    new_unchecked_vis: Option<Visibility>,
}

fn get_dst_attrs(attrs: &[Attribute]) -> syn::Result<DstAttrs> {
    mod kw {
        syn::custom_keyword!(simple_dst_crate);
        syn::custom_keyword!(new_unchecked_vis);
    }

    let mut dst_attrs = DstAttrs {
        simple_dst_crate: None,
        new_unchecked_vis: None,
    };
    for attr in attrs {
        if !attr.path().is_ident("dst") {
            continue;
        }

        attr.parse_args_with(|input: ParseStream| {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::simple_dst_crate) {
                input.parse::<kw::simple_dst_crate>()?;
                input.parse::<Token![=]>()?;
                let simple_dst_crate = input.parse()?;
                if dst_attrs.simple_dst_crate.is_some() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "only one #[dst(simple_dst_crate = ...)] is allowed",
                    ));
                }
                dst_attrs.simple_dst_crate = Some(simple_dst_crate);
            } else if lookahead.peek(kw::new_unchecked_vis) {
                input.parse::<kw::new_unchecked_vis>()?;
                input.parse::<Token![=]>()?;
                let new_unchecked_vis = input.parse()?;
                if dst_attrs.new_unchecked_vis.is_some() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "only one #[dst(new_unchecked_vis = ...)] is allowed",
                    ));
                }
                dst_attrs.new_unchecked_vis = Some(new_unchecked_vis);
            } else {
                return Err(Error::new_spanned(
                    attr,
                    "unrecognised #[dst(...)] argument",
                ));
            }
            Ok(())
        })?
    }
    Ok(dst_attrs)
}

#[proc_macro_derive(Dst, attributes(dst))]
pub fn derive_dst(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    if !is_repr_c(&input.attrs) {
        return quote! { compile_error!("type must be `repr(C)`") }.into();
    }

    let name = input.ident;

    let (simple_dst_crate, new_unchecked_vis) = match get_dst_attrs(&input.attrs) {
        Ok(DstAttrs {
            simple_dst_crate,
            new_unchecked_vis,
        }) => (
            simple_dst_crate.unwrap_or_else(|| parse_quote! { ::simple_dst }),
            new_unchecked_vis.unwrap_or(Visibility::Inherited),
        ),
        Err(e) => return e.into_compile_error().into(),
    };

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let fields = get_fields(&input.data);
    if fields.is_empty() {
        return quote! { compile_error!("type must have at least one field") }.into();
    }

    let n_fields = fields.len();

    let idxs: Vec<_> = (0..n_fields).collect();
    let last_idx = n_fields - 1;
    let first_idxs: Vec<_> = (0..last_idx).collect();

    let idents: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let first_idents = &idents[..last_idx];
    let last_ident = &idents[last_idx];

    let layout_idents: Vec<_> = idents
        .iter()
        .map(|f| format_ident!("layout_{}", f))
        .collect();
    let first_layout_idents = &layout_idents[..last_idx];
    let last_layout_ident = &layout_idents[last_idx];

    let tys: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let first_tys = &tys[..last_idx];
    let last_ty = &tys[last_idx];

    let expanded = quote! {
        #[automatically_derived]
        unsafe impl #impl_generics #simple_dst_crate::Dst for #name #ty_generics #where_clause {
            fn len(&self) -> usize {
                #simple_dst_crate::Dst::len(&self.#last_ident)
            }

            fn layout(len: usize) -> ::core::result::Result<::core::alloc::Layout, ::core::alloc::LayoutError> {
                let (layout, _) = Self::__dst_impl_layout_offsets(len)?;
                ::core::result::Result::Ok(layout)
            }

            fn retype(ptr: *mut u8, len: usize) -> *mut Self {
                // FUTURE: switch to ptr::from_raw_parts_mut() when it has stabilised.
                ::core::ptr::slice_from_raw_parts_mut(ptr, len) as *mut _
            }
        }

        #[automatically_derived]
        impl #impl_generics #name #ty_generics #where_clause {
            #[doc(hidden)]
            #[inline]
            fn __dst_impl_layout_offsets(len: usize) -> ::core::result::Result<(::core::alloc::Layout, [usize; #n_fields]), ::core::alloc::LayoutError> {
                #( let #first_layout_idents = ::core::alloc::Layout::new::<#first_tys>(); )*
                let #last_layout_ident = <#last_ty as #simple_dst_crate::Dst>::layout(len)?;
                let mut offsets = [0; #n_fields];
                let layout = ::core::alloc::Layout::from_size_align(0, 1)?;
                #(
                    let (layout, offset) = layout.extend(#layout_idents)?;
                    offsets[#idxs] = offset;
                )*
                ::core::result::Result::Ok((layout.pad_to_align(), offsets))
            }

            #new_unchecked_vis unsafe fn new_unchecked<A: #simple_dst_crate::AllocDst<Self>>(
                #( #first_idents: #first_tys ),*,
                #last_ident: &#last_ty
            ) -> ::core::result::Result<A, ::core::alloc::LayoutError> {
                let (layout, offsets) = Self::__dst_impl_layout_offsets(#last_ident.len())?;
                Ok(unsafe {
                    A::new_dst(<#last_ty as #simple_dst_crate::Dst>::len(#last_ident), layout, |ptr| {
                        let dest = ptr.cast::<u8>().as_ptr();

                        <#last_ty as #simple_dst_crate::CloneToUninit>::clone_to_uninit(#last_ident, dest.add(offsets[#last_idx]));

                        #(
                            dest.add(offsets[#first_idxs]).cast::<#first_tys>().write(#first_idents);
                        )*
                    })
                })
            }
        }
    };

    expanded.into()
}

#[proc_macro_derive(CloneToUninit, attributes(dst))]
pub fn derive_clone_to_uninit(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let simple_dst_crate = match get_dst_attrs(&input.attrs) {
        Ok(DstAttrs {
            simple_dst_crate, ..
        }) => simple_dst_crate.unwrap_or_else(|| parse_quote! { ::simple_dst }),
        Err(e) => return e.into_compile_error().into(),
    };

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let fields = get_fields(&input.data);
    if fields.is_empty() {
        return quote! {compile_error!("type must have at least one field")}.into();
    }

    let n_fields = fields.len();

    let last_idx = n_fields - 1;

    let idents: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let first_idents = &idents[..last_idx];
    let last_ident = &idents[last_idx];

    let tys: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let first_tys = &tys[..last_idx];
    let last_ty = &tys[last_idx];

    let expanded = quote! {
        #[automatically_derived]
        unsafe impl #impl_generics #simple_dst_crate::CloneToUninit for #name #ty_generics #where_clause {
            unsafe fn clone_to_uninit(&self, dest: *mut u8) {
                // FUTURE: switch to byte_offset_from_unsigned when it has stabilised.
                let last_offset = unsafe {
                    usize::try_from((&raw const self.#last_ident).byte_offset_from(self)).unwrap_unchecked()
                };

                #(
                    let #first_idents = <#first_tys as ::core::clone::Clone>::clone(&self.#first_idents);
                )*

                unsafe {
                    <#last_ty as #simple_dst_crate::CloneToUninit>::clone_to_uninit(&self.#last_ident, dest.add(last_offset));

                    #(
                        dest.add(::core::mem::offset_of!(Self, #first_idents)).cast::<#first_tys>().write(#first_idents);
                    )*
                }
            }
        }
    };

    expanded.into()
}

struct ToOwnedAttrs {
    owned: Option<Type>,
    to_owned_crate: Option<Path>,
}

fn get_to_owned_attrs(attrs: &[Attribute]) -> syn::Result<ToOwnedAttrs> {
    mod kw {
        syn::custom_keyword!(owned);
        syn::custom_keyword!(to_owned_crate);
    }

    let mut to_owned_attrs = ToOwnedAttrs {
        owned: None,
        to_owned_crate: None,
    };
    for attr in attrs {
        if !attr.path().is_ident("to_owned") {
            continue;
        }

        attr.parse_args_with(|input: ParseStream| {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::owned) {
                input.parse::<kw::owned>()?;
                input.parse::<Token![=]>()?;
                let owned = input.parse()?;
                if to_owned_attrs.owned.is_some() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "only one #[to_owned(owned = ...)] is allowed",
                    ));
                }
                to_owned_attrs.owned = Some(owned);
            } else if lookahead.peek(kw::to_owned_crate) {
                input.parse::<kw::to_owned_crate>()?;
                input.parse::<Token![=]>()?;
                let to_owned_crate = input.parse()?;
                if to_owned_attrs.to_owned_crate.is_some() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "only one #[to_owned(to_owned_crate = ...)] is allowed",
                    ));
                }
                to_owned_attrs.to_owned_crate = Some(to_owned_crate);
            } else {
                return Err(Error::new_spanned(
                    attr,
                    "unrecognised #[to_owned(...)] argument",
                ));
            }
            Ok(())
        })?
    }
    Ok(to_owned_attrs)
}

#[proc_macro_derive(ToOwned, attributes(dst, to_owned))]
pub fn derive_to_owned(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let simple_dst_crate = match get_dst_attrs(&input.attrs) {
        Ok(DstAttrs {
            simple_dst_crate, ..
        }) => simple_dst_crate.unwrap_or_else(|| parse_quote! { ::simple_dst }),
        Err(e) => return e.into_compile_error().into(),
    };
    let (owned, to_owned_crate) = match get_to_owned_attrs(&input.attrs) {
        Ok(ToOwnedAttrs {
            owned,
            to_owned_crate,
        }) => (
            owned.unwrap_or(parse_quote! { Box<#name> }),
            to_owned_crate.unwrap_or(parse_quote! { ::alloc::borrow }),
        ),
        Err(e) => return e.into_compile_error().into(),
    };

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    quote! {
        #[automatically_derived]
        impl #impl_generics #to_owned_crate::ToOwned for #name #ty_generics #where_clause {
            type Owned = #owned;

            fn to_owned(&self) -> Self::Owned {
                let layout = ::core::alloc::Layout::for_value(self);

                unsafe {
                    <#owned as #simple_dst_crate::AllocDst<#name>>::new_dst(
                        <#name as #simple_dst_crate::Dst>::len(self),
                        layout,
                        |ptr| {
                            let dest = ptr.cast::<u8>().as_ptr();

                            <#name as #simple_dst_crate::CloneToUninit>::clone_to_uninit(self, dest)
                        },
                    )
                }
            }
        }
    }
    .into()
}
