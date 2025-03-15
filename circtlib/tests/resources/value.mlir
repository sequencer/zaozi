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
 
om.class @MapConstant() -> (map_i64: !om.map<!om.string, i64>) {
  %0 = om.constant #om.map<i64, {a = 42, b = 32}> : !om.map<!om.string, i64>
  om.class.fields %0 : !om.map<!om.string, i64>
}

om.class @MapCreate() -> (map_field: !om.map<!om.string, !om.class.type<@Empty>>) {
  %s0 = om.constant "foo" : !om.string
  %s1 = om.constant "bar" : !om.string
  %0 = om.object @Empty() : () -> !om.class.type<@Empty>
  %1 = om.tuple_create %s0, %0 : !om.string, !om.class.type<@Empty>
  %2 = om.tuple_create %s1, %0 : !om.string, !om.class.type<@Empty>
  %map = om.map_create %1, %2 : !om.string, !om.class.type<@Empty>
  om.class.fields %map : !om.map<!om.string, !om.class.type<@Empty>>
}

om.class @Tuple(%int: i1) -> (tuple: tuple<i1, !om.string>, val: !om.string) {
  %str = om.constant "foo" : !om.string
  %tuple = om.tuple_create %int, %str  : i1, !om.string
  %val = om.tuple_get %tuple[1]  : tuple<i1, !om.string>
  om.class.fields %tuple, %val : tuple<i1, !om.string>, !om.string
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
