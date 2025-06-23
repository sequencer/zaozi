om.class @Thingy(%blue_1: i8, %blue_2: i32) -> (widget: !om.class.type<@Widget>, gadget: !om.class.type<@Gadget>, blue_1: i8, blue_2: i8) {
  %0 = om.constant 5 : i8
  %1 = om.constant 6 : i32
  %2 = om.object @Widget(%0, %1) : (i8, i32) -> !om.class.type<@Widget>

  %3 = om.constant 7 : i8
  %4 = om.constant 8 : i32
  %5 = om.object @Gadget(%3, %4) : (i8, i32) -> !om.class.type<@Gadget>

  %6 = om.object.field %2, [@blue_1] : (!om.class.type<@Widget>) -> i8

  om.class.fields {test = "fieldsAttr"} %2, %5, %blue_1, %6 : !om.class.type<@Widget>, !om.class.type<@Gadget>, i8, i8 loc("test")
}

om.class @Widget(%blue_1: i8, %green_1: i32) -> (blue_1: i8, green_1: i32) {
  om.class.fields %blue_1, %green_1 : i8, i32
}

om.class @Gadget(%green_1: i8, %green_2: i32) -> (green_1: i8, green_2: i32) {
  om.class.fields %green_1, %green_2 : i8, i32
}
 
om.class @Empty() {
  om.class.fields
}

om.class @DiscardableAttrs() attributes {foo.bar="baz"} {
  om.class.fields
}

om.class @NestedField1() -> (baz: i1) {
  %0 = om.constant 1 : i1
  om.class.fields %0 : i1
}

om.class @NestedField2() -> (bar: !om.class.type<@NestedField1>) {
  %0 = om.object @NestedField1() : () -> !om.class.type<@NestedField1>
  om.class.fields %0 : !om.class.type<@NestedField1>
}

om.class @NestedField3() -> (foo: !om.class.type<@NestedField2>) {
  %0 = om.object @NestedField2() : () -> !om.class.type<@NestedField2>
  om.class.fields %0 : !om.class.type<@NestedField2>
}

om.class @NestedField4() -> (result: i1) {
  %0 = om.object @NestedField3() : () -> !om.class.type<@NestedField3>
  %1 = om.object.field %0, [@foo, @bar, @baz] : (!om.class.type<@NestedField3>) -> i1
  om.class.fields %1 : i1
}

om.class @ReferenceConstant() -> (myref: !om.ref, sym: !om.sym_ref) {
  %0 = om.constant #om.ref<#hw.innerNameRef<@A::@inst_1>> : !om.ref

  %1 = om.constant #om.sym_ref<@A> : !om.sym_ref

  om.class.fields %0, %1 : !om.ref, !om.sym_ref
}

om.class @ListConstant() -> (list_i64: !om.list<i64>, list_i32: !om.list<i32>) {
  %0 = om.constant #om.list<i64, [42]> : !om.list<i64>

  %1 = om.constant #om.list<i32, []> : !om.list<i32>

  om.class.fields %0, %1 : !om.list<i64>, !om.list<i32>
}

om.class @ListCreate() -> (list_field: !om.list<!om.class.type<@Widget>>) {
  %cst5_i8 = om.constant 5 : i8
  %cst6_i8 = om.constant 6 : i8
  %cst5_i32 = om.constant 5 : i32
  %cst6_i32 = om.constant 6 : i32

  %obj0 = om.object @Widget(%cst5_i8, %cst6_i32) : (i8, i32) -> !om.class.type<@Widget>

  %obj1 = om.object @Widget(%cst6_i8, %cst5_i32) : (i8, i32) -> !om.class.type<@Widget>

  %list = om.list_create %obj0, %obj1 : !om.class.type<@Widget>

  om.class.fields %list : !om.list<!om.class.type<@Widget>>
}

om.class @IntegerConstant() -> (int: !om.integer) {
  %0 = om.constant #om.integer<8428132854 : i35> : !om.integer
  om.class.fields %0 : !om.integer
}

om.class @StringConstant() -> (string: !om.string) {
  %0 = om.constant "foo" : !om.string
  om.class.fields %0 : !om.string
}

om.class @BoolConstant(%b0 : i1) -> (bool: i1, bool2: i1, bool3: i1) {
  %1 = om.constant true
  %2 = om.constant false
  om.class.fields %b0, %1, %2 : i1, i1, i1
}
 
om.class @FrozenPath(%basepath: !om.frozenbasepath) -> (path: !om.frozenpath, path_empty: !om.frozenpath, basepath: !om.frozenbasepath){
  %0 = om.frozenbasepath_create %basepath "Foo/bar"
  %1 = om.frozenpath_create reference %basepath "Foo/bar:Bar>w.a"
  %2 = om.frozenpath_empty
  om.class.fields %1, %2, %basepath : !om.frozenpath, !om.frozenpath, !om.frozenbasepath
}

om.class @Any() -> (object: !om.any, string: !om.any) {
  %0 = om.object @Empty() : () -> !om.class.type<@Empty>
  %1 = om.any_cast %0 : (!om.class.type<@Empty>) -> !om.any
  %2 = om.constant "foo" : !om.string
  %3 = om.any_cast %2 : (!om.string) -> !om.any
  om.class.fields %1, %3 : !om.any, !om.any
}

om.class @ObjectField() -> (field: !om.any) {
  %0 = om.object @Any() : () -> !om.class.type<@Any>
  %1 = om.object.field %0, [@object] : (!om.class.type<@Any>) -> !om.any
  om.class.fields %1 : !om.any
}

om.class @InnerClass1(%anyListIn: !om.list<!om.any>)  -> (any_list1: !om.list<!om.any>) {
  om.class.fields %anyListIn : !om.list<!om.any>
}
om.class @InnerClass2(%anyListIn: !om.list<!om.any>)  -> (any_list2: !om.list<!om.any>) {
  om.class.fields %anyListIn : !om.list<!om.any>
}
om.class @OuterClass2()  -> (om: !om.class.type<@InnerClass2>) {
  %0 = om.object @InnerClass2(%5) : (!om.list<!om.any>) -> !om.class.type<@InnerClass2>
  %1 = om.object @Any() : () -> !om.class.type<@Any>
  %2 = om.object.field %1, [@object] : (!om.class.type<@Any>) -> !om.any
  %3 = om.object @Any() : () -> !om.class.type<@Any>
  %4 = om.object.field %3, [@object] : (!om.class.type<@Any>) -> !om.any
  %5 = om.list_create %2, %4 : !om.any
  om.class.fields %0 : !om.class.type<@InnerClass2>
}
om.class @OuterClass1()  -> (om: !om.any) {
  %0 = om.object @InnerClass1(%8) : (!om.list<!om.any>) -> !om.class.type<@InnerClass1>
  %1 = om.any_cast %0 : (!om.class.type<@InnerClass1>) -> !om.any
  %2 = om.object @OuterClass2() : () -> !om.class.type<@OuterClass2>
  %3 = om.object.field %2, [@om] : (!om.class.type<@OuterClass2>) -> !om.class.type<@InnerClass2>
  %4 = om.any_cast %3 : (!om.class.type<@InnerClass2>) -> !om.any
  %5 = om.object @OuterClass2() : () -> !om.class.type<@OuterClass2>
  %6 = om.object.field %5, [@om] : (!om.class.type<@OuterClass2>) -> !om.class.type<@InnerClass2>
  %7 = om.any_cast %6 : (!om.class.type<@InnerClass2>) -> !om.any
  %8 = om.list_create %4, %7 : !om.any
  om.class.fields %1 : !om.any
}
