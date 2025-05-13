use quote::{format_ident, quote};
use syn::{
    AttrStyle, Attribute, Data, DataStruct, DeriveInput, Field, Fields, FieldsNamed, Meta,
    MetaList, Token, parse_macro_input, punctuated::Punctuated,
};

fn is_repr_c(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        matches!(
            a,
            Attribute {
                style: AttrStyle::Outer,
                meta: Meta::List(MetaList {
                    path,
                    tokens,
                    ..
                }),
                ..
            } if path.is_ident("repr") && {
                let mut tokens = tokens.clone().into_iter();
                matches!(
                    (tokens.next(), tokens.next()),
                    (Some(proc_macro2::TokenTree::Ident(token)), None) if matches!(token.to_string().as_str(), "C" | "transparent")
                )
            }
        )
    })
}

fn get_fields(data: Data) -> Punctuated<Field, Token![,]> {
    match data {
        Data::Struct(DataStruct { fields, .. }) => match fields {
            Fields::Named(FieldsNamed { named: fields, .. }) => fields,
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
    }
}

#[proc_macro_derive(Dst)]
pub fn derive_dst(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    if !is_repr_c(&input.attrs) {
        return quote! {compile_error!("type must be `repr(C)`")}.into();
    }

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let fields = get_fields(input.data);
    if fields.is_empty() {
        return quote! {compile_error!("type must have at least one field")}.into();
    }

    let n_fields = fields.len();

    let idxs: Vec<_> = (0..n_fields).collect();
    let last_idx = n_fields - 1;
    let _first_idxs: Vec<_> = (0..last_idx).collect();

    let idents: Vec<_> = fields
        .iter()
        .map(|f| match f {
            Field {
                attrs,
                ident: Some(ident),
                ..
            } if attrs.is_empty() => ident,
            _ => unimplemented!(),
        })
        .collect();
    let first_idents = &idents[..last_idx];
    let last_ident = &idents[last_idx];

    let layout_idents: Vec<_> = idents.iter().map(|f| format_ident!("{f}_layout")).collect();
    let first_layout_idents = &layout_idents[..last_idx];
    let last_layout_ident = &layout_idents[last_idx];

    let offset_idents: Vec<_> = idents.iter().map(|f| format_ident!("{f}_offset")).collect();
    let _first_offset_idents = &offset_idents[..last_idx];
    let last_offset_ident = &offset_idents[last_idx];

    let tys: Vec<_> = fields
        .iter()
        .map(|f| match f {
            Field { attrs, ty, .. } if attrs.is_empty() => ty,
            _ => unimplemented!(),
        })
        .collect();
    let first_tys = &tys[..last_idx];
    let last_ty = &tys[last_idx];

    let expanded = quote! {
        #[automatically_derived]
        unsafe impl #impl_generics ::simple_dst::Dst for #name #ty_generics #where_clause {
            fn len(&self) -> usize {
                ::simple_dst::Dst::len(&self.#last_ident)
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
                let #last_layout_ident = <#last_ty as ::simple_dst::Dst>::layout(len)?;
                let mut offsets = [0; #n_fields];
                let layout = ::core::alloc::Layout::from_size_align(0, 1)?;
                #(
                    let (layout, offset) = layout.extend(#layout_idents)?;
                    offsets[#idxs] = offset;
                )*
                ::core::result::Result::Ok((layout.pad_to_align(), offsets))
            }

            #[doc(hidden)]
            #[inline]
            unsafe fn __dst_impl_write_to_uninit(
                dest: *mut u8,
                #last_offset_ident: usize,
                #( #first_idents: #first_tys ),*,
                #last_ident: &#last_ty
            ) {
                unsafe {
                    <#last_ty as ::simple_dst::CloneToUninitDst>::clone_to_uninit(#last_ident, dest.add(#last_offset_ident));

                    #(
                        ::core::ptr::write(dest.add(::core::mem::offset_of!(Self, #first_idents)).cast::<#first_tys>(), #first_idents);
                    )*
                }
            }

            #[inline]
            fn new_internal<A: ::simple_dst::AllocDst<Self>>(
                #( #first_idents: #first_tys ),*,
                #last_ident: &#last_ty
            ) -> ::core::result::Result<A, ::simple_dst::AllocDstError<::core::alloc::LayoutError>> {
                unsafe {
                    A::new_dst(<#last_ty as ::simple_dst::Dst>::len(#last_ident), |ptr| {
                        let (_, offsets) = Self::__dst_impl_layout_offsets(#last_ident.len())?;
                        Self::__dst_impl_write_to_uninit(ptr.cast::<u8>().as_ptr(), offsets[#last_idx], #( #idents ),*);
                        ::core::result::Result::<(), ::core::alloc::LayoutError>::Ok(())
                    })
                }
            }
        }
    };

    expanded.into()
}
