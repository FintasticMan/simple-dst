use proc_macro2::{Span, TokenStream};
use quote::{IdentFragment, ToTokens, format_ident, quote};
use syn::{
    Attribute, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Fields, FieldsNamed,
    FieldsUnnamed, GenericParam, Generics, Ident, Index, Path, Token, Type, Visibility,
    parse_macro_input, parse_quote,
};

fn require_repr_c(attrs: &[Attribute]) -> syn::Result<()> {
    let mut found = false;
    for attr in attrs {
        if !attr.path().is_ident("repr") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("C") {
            } else {
                return Err(meta.error("only #[repr(C)] is supported"));
            }
            Ok(())
        })?;
        if found {
            return Err(syn::Error::new_spanned(attr, "only one #[repr(C)] allowed"));
        }
        found = true;
    }
    if !found {
        return Err(syn::Error::new(
            Span::call_site(),
            "type must be #[repr(C)]",
        ));
    }
    Ok(())
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

fn get_fields(data: &Data) -> syn::Result<Vec<Field>> {
    Ok(match data {
        Data::Struct(DataStruct {
            fields, semi_token, ..
        }) => match fields {
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
            _ => {
                return Err(Error::new_spanned(
                    semi_token,
                    "type must not be a unit struct",
                ));
            }
        },
        Data::Enum(DataEnum { enum_token, .. }) => {
            return Err(Error::new_spanned(enum_token, "only structs are supported"));
        }
        Data::Union(DataUnion { union_token, .. }) => {
            return Err(Error::new_spanned(
                union_token,
                "only structs are supported",
            ));
        }
    })
}

struct DstAttrs {
    simple_dst_path: Path,
    new_unchecked_vis: Visibility,
}

fn get_dst_attrs(attrs: &[Attribute]) -> syn::Result<DstAttrs> {
    let mut simple_dst_path: Option<Path> = None;
    let mut new_unchecked_vis: Option<Visibility> = None;
    for attr in attrs {
        if !attr.path().is_ident("dst") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("simple_dst_path") {
                if simple_dst_path.is_some() {
                    return Err(meta.error("only one #[dst(simple_dst_path = ...)] is allowed"));
                }
                simple_dst_path = Some({
                    meta.input.parse::<Token![=]>()?;
                    meta.input.parse()?
                })
            } else if meta.path.is_ident("new_unchecked_vis") {
                if new_unchecked_vis.is_some() {
                    return Err(meta.error("only one #[dst(new_unchecked_vis = ...)] is allowed"));
                }
                new_unchecked_vis = Some({
                    meta.input.parse::<Token![=]>()?;
                    meta.input.parse()?
                })
            } else {
                return Err(meta.error("unrecognised #[dst(...)] argument"));
            }
            Ok(())
        })?;
    }

    let dst_attrs = DstAttrs {
        simple_dst_path: simple_dst_path.unwrap_or_else(|| parse_quote! { ::simple_dst }),
        new_unchecked_vis: new_unchecked_vis.unwrap_or(Visibility::Inherited),
    };
    Ok(dst_attrs)
}

fn has_dst_attr(attrs: &[Attribute]) -> syn::Result<bool> {
    let mut found = false;
    for attr in attrs {
        if !attr.path().is_ident("dst") {
            continue;
        }

        attr.meta.require_path_only()?;
        if found {
            return Err(Error::new_spanned(attr, "only one #[dst] is allowed"));
        }
        found = true;
    }
    Ok(found)
}

fn add_dst_trait_bounds(mut generics: Generics, simple_dst_path: &Path) -> syn::Result<Generics> {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            if has_dst_attr(&type_param.attrs)? {
                type_param
                    .bounds
                    .push(parse_quote! { #simple_dst_path::Dst });
                type_param
                    .bounds
                    .push(parse_quote! { #simple_dst_path::CloneToUninit });
            };
        }
    }
    Ok(generics)
}

#[proc_macro_derive(Dst, attributes(dst))]
pub fn derive_dst(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    derive_dst_impl(input)
        .unwrap_or_else(|e| e.into_compile_error())
        .into()
}

fn derive_dst_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    require_repr_c(&input.attrs)?;

    let name = input.ident;

    let DstAttrs {
        simple_dst_path,
        new_unchecked_vis,
    } = get_dst_attrs(&input.attrs)?;

    let generics = add_dst_trait_bounds(input.generics, &simple_dst_path)?;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let fields = get_fields(&input.data)?;
    if fields.is_empty() {
        return Err(Error::new_spanned(
            name,
            "type must have at least one field",
        ));
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

    Ok(quote! {
        #[automatically_derived]
        unsafe impl #impl_generics #simple_dst_path::Dst for #name #ty_generics #where_clause {
            fn len(&self) -> usize {
                #simple_dst_path::Dst::len(&self.#last_ident)
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
                let #last_layout_ident = <#last_ty as #simple_dst_path::Dst>::layout(len)?;
                let mut offsets = [0; #n_fields];
                let layout = ::core::alloc::Layout::from_size_align(0, 1)?;
                #(
                    let (layout, offset) = layout.extend(#layout_idents)?;
                    offsets[#idxs] = offset;
                )*
                ::core::result::Result::Ok((layout.pad_to_align(), offsets))
            }

            #new_unchecked_vis unsafe fn new_unchecked<A: #simple_dst_path::AllocDst<Self>>(
                #( #first_idents: #first_tys, )*
                #last_ident: &#last_ty
            ) -> ::core::result::Result<A, ::core::alloc::LayoutError> {
                let (layout, offsets) = Self::__dst_impl_layout_offsets(#last_ident.len())?;
                Ok(unsafe {
                    A::new_dst(<#last_ty as #simple_dst_path::Dst>::len(#last_ident), layout, |ptr| {
                        let dest = ptr.cast::<u8>().as_ptr();

                        <#last_ty as #simple_dst_path::CloneToUninit>::clone_to_uninit(#last_ident, dest.add(offsets[#last_idx]));

                        #(
                            dest.add(offsets[#first_idxs]).cast::<#first_tys>().write(#first_idents);
                        )*
                    })
                })
            }
        }
    })
}

fn add_clone_to_uninit_trait_bounds(
    mut generics: Generics,
    simple_dst_path: &Path,
) -> syn::Result<Generics> {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            let bound = if has_dst_attr(&type_param.attrs)? {
                parse_quote! { #simple_dst_path::CloneToUninit }
            } else {
                parse_quote! { ::core::clone::Clone }
            };
            type_param.bounds.push(bound);
        }
    }
    Ok(generics)
}

#[proc_macro_derive(CloneToUninit, attributes(dst))]
pub fn derive_clone_to_uninit(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    derive_clone_to_uninit_impl(input)
        .unwrap_or_else(|e| e.into_compile_error())
        .into()
}
fn derive_clone_to_uninit_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = input.ident;

    let DstAttrs {
        simple_dst_path, ..
    } = get_dst_attrs(&input.attrs)?;

    let generics = add_clone_to_uninit_trait_bounds(input.generics, &simple_dst_path)?;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let fields = get_fields(&input.data)?;
    if fields.is_empty() {
        return Err(Error::new_spanned(
            name,
            "type must have at least one field",
        ));
    }

    let n_fields = fields.len();

    let last_idx = n_fields - 1;

    let idents: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let first_idents = &idents[..last_idx];
    let last_ident = &idents[last_idx];

    let tys: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let first_tys = &tys[..last_idx];
    let last_ty = &tys[last_idx];

    Ok(quote! {
        #[automatically_derived]
        unsafe impl #impl_generics #simple_dst_path::CloneToUninit for #name #ty_generics #where_clause {
            unsafe fn clone_to_uninit(&self, dest: *mut u8) {
                // FUTURE: switch to byte_offset_from_unsigned when it has stabilised.
                let last_offset = unsafe {
                    usize::try_from((&raw const self.#last_ident).byte_offset_from(self)).unwrap_unchecked()
                };

                #(
                    let #first_idents = <#first_tys as ::core::clone::Clone>::clone(&self.#first_idents);
                )*

                unsafe {
                    <#last_ty as #simple_dst_path::CloneToUninit>::clone_to_uninit(&self.#last_ident, dest.add(last_offset));

                    #(
                        dest.add(::core::mem::offset_of!(Self, #first_idents)).cast::<#first_tys>().write(#first_idents);
                    )*
                }
            }
        }
    })
}

struct ToOwnedAttrs {
    alloc_path: Path,
    owned: Type,
}

fn get_to_owned_attrs(attrs: &[Attribute], name: &Ident) -> syn::Result<ToOwnedAttrs> {
    let mut alloc_path: Option<Path> = None;
    let mut owned: Option<Type> = None;
    for attr in attrs {
        if !attr.path().is_ident("to_owned") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("alloc_path") {
                if alloc_path.is_some() {
                    return Err(meta.error("only one #[to_owned(alloc_path = ...)] is allowed"));
                }
                alloc_path = Some({
                    meta.input.parse::<Token![=]>()?;
                    meta.input.parse()?
                });
            } else if meta.path.is_ident("owned") {
                if owned.is_some() {
                    return Err(meta.error("only one #[to_owned(owned = ...)] is allowed"));
                }
                owned = Some({
                    meta.input.parse::<Token![=]>()?;
                    meta.input.parse()?
                })
            } else {
                return Err(meta.error("unrecognised #[to_owned(...)] argument"));
            }
            Ok(())
        })?;
    }

    let alloc_path = alloc_path.unwrap_or_else(|| parse_quote! { ::std });
    let to_owned_attrs = ToOwnedAttrs {
        alloc_path: alloc_path.clone(),
        owned: owned.unwrap_or_else(|| parse_quote! { #alloc_path::boxed::Box<#name> }),
    };
    Ok(to_owned_attrs)
}

#[proc_macro_derive(ToOwned, attributes(dst, to_owned))]
pub fn derive_to_owned(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    derive_to_owned_impl(input)
        .unwrap_or_else(|e| e.into_compile_error())
        .into()
}

fn derive_to_owned_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = input.ident;

    let DstAttrs {
        simple_dst_path, ..
    } = get_dst_attrs(&input.attrs)?;
    let ToOwnedAttrs { alloc_path, owned } = get_to_owned_attrs(&input.attrs, &name)?;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    Ok(quote! {
        #[automatically_derived]
        impl #impl_generics #alloc_path::borrow::ToOwned for #name #ty_generics #where_clause {
            type Owned = #owned;

            fn to_owned(&self) -> Self::Owned {
                let layout = ::core::alloc::Layout::for_value(self);

                unsafe {
                    <#owned as #simple_dst_path::AllocDst<#name>>::new_dst(
                        <#name as #simple_dst_path::Dst>::len(self),
                        layout,
                        |ptr| {
                            let dest = ptr.cast::<u8>().as_ptr();

                            <#name as #simple_dst_path::CloneToUninit>::clone_to_uninit(self, dest)
                        },
                    )
                }
            }
        }
    })
}
