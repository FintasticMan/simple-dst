use quote::{format_ident, quote};
use syn::{
    AttrStyle, Attribute, Data, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    Meta, MetaList, Token, parse_macro_input, punctuated::Punctuated,
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
            Fields::Unnamed(FieldsUnnamed {
                unnamed: fields, ..
            }) => fields,
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
    let first_idents = &idents[..n_fields - 1];
    let last_ident = &idents[n_fields - 1];

    let layout_idents: Vec<_> = idents.iter().map(|f| format_ident!("{f}_layout")).collect();
    let first_layout_ident = &layout_idents[0];
    let first_layout_idents = &layout_idents[..n_fields - 1];
    let last_layout_ident = &layout_idents[n_fields - 1];

    let tys: Vec<_> = fields
        .iter()
        .map(|f| match f {
            Field { attrs, ty, .. } if attrs.is_empty() => ty,
            _ => unimplemented!(),
        })
        .collect();
    let first_tys = &tys[..n_fields - 1];
    let last_ty = &tys[n_fields - 1];

    let layout_offset: Vec<_> = layout_idents[1..]
        .iter()
        .enumerate()
        .map(|(i, ident)| {
            let i = i + 1;
            quote! {
                let (layout, offset) = layout.extend(#ident)?;
                offsets[#i] = offset;
            }
        })
        .collect();

    let writes: Vec<_> = first_idents
        .iter()
        .enumerate()
        .map(|(i, ident)| {
            quote! {
                ::core::ptr::write(raw.add(offsets[#i]).cast().as_ptr(), #ident);
            }
        })
        .collect();

    let expanded = quote! {
        unsafe impl #impl_generics dst::Dst for #name #ty_generics #where_clause {
            fn len(&self) -> usize {
                dst::Dst::len(&self.#last_ident)
            }

            fn layout(len: usize) -> ::core::result::Result<::core::alloc::Layout, ::core::alloc::LayoutError> {
                let (layout, _) = Self::layout_offsets(len)?;
                Ok(layout)
            }

            fn retype(ptr: ::core::ptr::NonNull<u8>, len: usize) -> ::core::ptr::NonNull<Self> {
                // FUTURE: switch to ptr::NonNull:from_raw_parts() when it has stabilised.
                let ptr = ::core::ptr::NonNull::slice_from_raw_parts(ptr.cast::<()>(), len);
                unsafe { ::core::ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
            }

            unsafe fn clone_to_raw(&self, ptr: ::core::ptr::NonNull<Self>) {
                unsafe {
                    Self::write_to_raw(ptr, #( self.#first_idents ),*, &self.#last_ident)
                }
            }
        }

        impl #impl_generics #name #ty_generics #where_clause {
            fn layout_offsets(len: usize) -> ::core::result::Result<(::core::alloc::Layout, [usize; #n_fields]), ::core::alloc::LayoutError> {
                #( let #first_layout_idents = ::core::alloc::Layout::new::<#first_tys>(); )*
                let #last_layout_ident = <#last_ty as dst::Dst>::layout(len)?;
                let mut offsets = [0; #n_fields];
                let layout = #first_layout_ident;
                #( #layout_offset )*
                Ok((layout.pad_to_align(), offsets))
            }

            unsafe fn write_to_raw(
                ptr: ::core::ptr::NonNull<Self>,
                #( #first_idents: #first_tys ),*,
                #last_ident: &#last_ty
            ) {
                // TODO: remove this unwrap so that we don't break the contract for `new_dst`.
                let (layout, offsets) = Self::layout_offsets(<#last_ty as dst::Dst>::len(#last_ident)).unwrap();
                unsafe {
                    let raw = ptr.cast::<u8>();
                    #( #writes )*
                    <#last_ty as dst::Dst>::clone_to_raw(#last_ident, <#last_ty as dst::Dst>::retype(raw.add(offsets[#n_fields - 1]), dst::Dst::len(#last_ident)));
                    debug_assert_eq!(::core::alloc::Layout::for_value(ptr.as_ref()), layout);
                }
            }

            fn alloc<A: dst::AllocDst<Self>>(
                #( #first_idents: #first_tys ),*,
                #last_ident: &#last_ty
            ) -> ::core::result::Result<A, dst::AllocDstError> {
                unsafe {
                    <A as dst::AllocDst<Self>>::new_dst(<#last_ty as dst::Dst>::len(#last_ident), |ptr| {
                        Self::write_to_raw(ptr, #( #idents ),*)
                    })
                }
            }
        }
    };

    // Hand the output tokens back to the compiler.
    expanded.into()
}
