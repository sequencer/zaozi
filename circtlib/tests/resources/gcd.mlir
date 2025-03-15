module attributes {circt.loweringOptions = "verifLabels"} {
  sv.macro.decl @SYNTHESIS
  sv.macro.decl @VERILATOR
  emit.fragment @RANDOM_INIT_FRAGMENT {
    sv.verbatim "// Standard header to adapt well known macros for register randomization."
    sv.verbatim "\0A// RANDOM may be set to an expression that produces a 32-bit random unsigned value."
    sv.ifdef  @RANDOM {
    } else {
      sv.macro.def @RANDOM "$random"
    }
    sv.verbatim "\0A// Users can define INIT_RANDOM as general code that gets injected into the\0A// initializer block for modules with registers."
    sv.ifdef  @INIT_RANDOM {
    } else {
      sv.macro.def @INIT_RANDOM ""
    }
    sv.verbatim "\0A// If using random initialization, you can also define RANDOMIZE_DELAY to\0A// customize the delay used, otherwise 0.002 is used."
    sv.ifdef  @RANDOMIZE_DELAY {
    } else {
      sv.macro.def @RANDOMIZE_DELAY "0.002"
    }
    sv.verbatim "\0A// Define INIT_RANDOM_PROLOG_ for use in our modules below."
    sv.ifdef  @INIT_RANDOM_PROLOG_ {
    } else {
      sv.ifdef  @RANDOMIZE {
        sv.ifdef  @VERILATOR {
          sv.macro.def @INIT_RANDOM_PROLOG_ "`INIT_RANDOM"
        } else {
          sv.macro.def @INIT_RANDOM_PROLOG_ "`INIT_RANDOM #`RANDOMIZE_DELAY begin end"
        }
      } else {
        sv.macro.def @INIT_RANDOM_PROLOG_ ""
      }
    }
  }
  emit.fragment @RANDOM_INIT_REG_FRAGMENT {
    sv.verbatim "\0A// Include register initializers in init blocks unless synthesis is set"
    sv.ifdef  @RANDOMIZE {
    } else {
      sv.ifdef  @RANDOMIZE_REG_INIT {
        sv.macro.def @RANDOMIZE ""
      }
    }
    sv.ifdef  @SYNTHESIS {
    } else {
      sv.ifdef  @ENABLE_INITIAL_REG_ {
      } else {
        sv.macro.def @ENABLE_INITIAL_REG_ ""
      }
    }
    sv.verbatim ""
  }
  sv.macro.decl @ENABLE_INITIAL_REG_
  sv.macro.decl @ENABLE_INITIAL_MEM_
  sv.macro.decl @FIRRTL_BEFORE_INITIAL
  sv.macro.decl @FIRRTL_AFTER_INITIAL
  sv.macro.decl @RANDOMIZE_REG_INIT
  sv.macro.decl @RANDOMIZE
  sv.macro.decl @RANDOMIZE_DELAY
  sv.macro.decl @RANDOM
  sv.macro.decl @INIT_RANDOM
  sv.macro.decl @INIT_RANDOM_PROLOG_
  hw.hierpath private @xmrPath [@GCD::@sym]
  sv.macro.decl @ref_GCD_probe_busy
  emit.file "ref_GCD.sv" {
    sv.macro.def @ref_GCD_probe_busy "{{0}}"([@xmrPath])
  }
  hw.module @GCD(in %clock : i1, in %reset : i1, out input_ready : i1, in %input_valid : i1, in %input_bits_x : i16, in %input_bits_y : i16, out output_valid : i1, out output_bits : i16) attributes {emit.fragments = [@RANDOM_INIT_REG_FRAGMENT, @RANDOM_INIT_FRAGMENT]} {
    %c0_i16 = hw.constant 0 : i16
    %true = hw.constant true
    %input_valid_0 = sv.wire sym @sym_1 name "input_valid" {hw.verilogName = "input_valid_0"} : !hw.inout<i1>
    sv.assign %input_valid_0, %input_valid : i1
    %input_bits_x_1 = sv.wire sym @sym_2 name "input_bits_x" {hw.verilogName = "input_bits_x_0"} : !hw.inout<i16>
    sv.assign %input_bits_x_1, %input_bits_x : i16
    %input_bits_y_2 = sv.wire sym @sym_3 name "input_bits_y" {hw.verilogName = "input_bits_y_0"} : !hw.inout<i16>
    sv.assign %input_bits_y_2, %input_bits_y : i16
    %busy = sv.wire sym @sym_9 {hw.verilogName = "busy"} : !hw.inout<i1>
    %input_ready = sv.wire sym @sym_0 {hw.verilogName = "input_ready_0"} : !hw.inout<i1>
    %0 = sv.read_inout %busy : !hw.inout<i1>
    %1 = comb.xor bin %0, %true {sv.namehint = "_view__output_valid_T"} : i1
    sv.assign %input_ready, %1 : i1
    %x = sv.reg sym @sym_6 {hw.verilogName = "x"} : !hw.inout<i16> 
    %2 = sv.read_inout %x : !hw.inout<i16>
    %output_bits = sv.wire sym @sym_5 {hw.verilogName = "output_bits_0"} : !hw.inout<i16>
    sv.assign %output_bits, %2 : i16
    %y = sv.reg sym @sym_7 {hw.verilogName = "y"} : !hw.inout<i16> 
    %startupFlag = sv.reg sym @sym_8 {hw.verilogName = "startupFlag"} : !hw.inout<i1> 
    %3 = sv.read_inout %y : !hw.inout<i16>
    %4 = comb.icmp bin ne %3, %c0_i16 : i16
    sv.assign %busy, %4 : i1
    %5 = sv.read_inout %busy : !hw.inout<i1>
    %probeWire_busy = sv.wire sym @sym_10 {hw.verilogName = "probeWire_busy"} : !hw.inout<i1>
    sv.assign %probeWire_busy, %5 : i1
    %6 = sv.read_inout %busy : !hw.inout<i1>
    %7 = comb.xor bin %6, %true {sv.namehint = "_view__output_valid_T"} : i1
    %8 = sv.read_inout %startupFlag : !hw.inout<i1>
    %9 = comb.and bin %8, %7 {sv.namehint = "_view__output_valid_T_1"} : i1
    %output_valid = sv.wire sym @sym_4 {hw.verilogName = "output_valid_0"} : !hw.inout<i1>
    sv.assign %output_valid, %9 : i1
    %10 = sv.read_inout %probeWire_busy : !hw.inout<i1>
    %probeWire_busy_probe = sv.wire sym @sym {hw.verilogName = "probeWire_busy_probe"} : !hw.inout<i1>
    sv.assign %probeWire_busy_probe, %10 : i1
    sv.always posedge %clock {
      %14 = sv.logic {hw.verilogName = "_GEN"} : !hw.inout<i1>
      %15 = sv.logic {hw.verilogName = "_GEN_0"} : !hw.inout<i1>
      %16 = sv.read_inout %x : !hw.inout<i16>
      %17 = sv.read_inout %y : !hw.inout<i16>
      %18 = comb.icmp bin ugt %16, %17 : i16
      sv.bpassign %14, %18 : i1
      %19 = sv.read_inout %input_valid_0 : !hw.inout<i1>
      %20 = sv.read_inout %input_ready : !hw.inout<i1>
      %21 = comb.and bin %20, %19 : i1
      sv.bpassign %15, %21 : i1
      %22 = sv.read_inout %15 : !hw.inout<i1>
      sv.if %22 {
        %23 = sv.read_inout %input_bits_x_1 : !hw.inout<i16>
        sv.passign %x, %23 : i16
      } else {
        %23 = sv.read_inout %14 : !hw.inout<i1>
        sv.if %23 {
          %24 = sv.read_inout %x : !hw.inout<i16>
          %25 = sv.read_inout %y : !hw.inout<i16>
          %26 = comb.sub bin %24, %25 {sv.namehint = "_x_T"} : i16
          sv.passign %x, %26 : i16
        }
      }
      sv.if %reset {
        %false = hw.constant false
        %c0_i16_3 = hw.constant 0 : i16
        sv.passign %y, %c0_i16_3 : i16
        sv.passign %startupFlag, %false : i1
      } else {
        %23 = sv.read_inout %15 : !hw.inout<i1>
        sv.if %23 {
          %27 = sv.read_inout %input_bits_y_2 : !hw.inout<i16>
          sv.passign %y, %27 : i16
        } else {
          %true_3 = hw.constant true
          %27 = sv.read_inout %14 : !hw.inout<i1>
          %28 = comb.xor %27, %true_3 : i1
          sv.if %28 {
            %29 = sv.read_inout %x : !hw.inout<i16>
            %30 = sv.read_inout %y : !hw.inout<i16>
            %31 = comb.sub bin %30, %29 {sv.namehint = "_y_T"} : i16
            sv.passign %y, %31 : i16
          }
        }
        %24 = sv.read_inout %startupFlag : !hw.inout<i1>
        %25 = sv.read_inout %15 : !hw.inout<i1>
        %26 = comb.or %25, %24 : i1
        sv.passign %startupFlag, %26 : i1
      }
    }
    sv.ifdef  @ENABLE_INITIAL_REG_ {
      sv.ordered {
        sv.ifdef  @FIRRTL_BEFORE_INITIAL {
          sv.verbatim "`FIRRTL_BEFORE_INITIAL"
        }
        sv.initial {
          %_RANDOM = sv.logic {hw.verilogName = "_RANDOM"} : !hw.inout<uarray<2xi32>>
          sv.ifdef.procedural  @INIT_RANDOM_PROLOG_ {
            sv.verbatim "`INIT_RANDOM_PROLOG_"
          }
          sv.ifdef.procedural  @RANDOMIZE_REG_INIT {
            %c0_i2 = hw.constant 0 : i2
            %c-2_i2 = hw.constant -2 : i2
            %c1_i2 = hw.constant 1 : i2
            %false = hw.constant false
            %true_3 = hw.constant true
            sv.for %i = %c0_i2 to %c-2_i2 step %c1_i2 : i2 {
              %RANDOM = sv.macro.ref.expr.se @RANDOM() : () -> i32
              %23 = comb.extract %i from 0 : (i2) -> i1
              %24 = sv.array_index_inout %_RANDOM[%23] : !hw.inout<uarray<2xi32>>, i1
              sv.bpassign %24, %RANDOM : i32
            } {hw.verilogName = "i"}
            %14 = sv.array_index_inout %_RANDOM[%false] : !hw.inout<uarray<2xi32>>, i1
            %15 = sv.read_inout %14 : !hw.inout<i32>
            %16 = comb.extract %15 from 0 : (i32) -> i16
            sv.bpassign %x, %16 : i16
            %17 = sv.array_index_inout %_RANDOM[%false] : !hw.inout<uarray<2xi32>>, i1
            %18 = sv.read_inout %17 : !hw.inout<i32>
            %19 = comb.extract %18 from 16 : (i32) -> i16
            sv.bpassign %y, %19 : i16
            %20 = sv.array_index_inout %_RANDOM[%true_3] : !hw.inout<uarray<2xi32>>, i1
            %21 = sv.read_inout %20 : !hw.inout<i32>
            %22 = comb.extract %21 from 0 : (i32) -> i1
            sv.bpassign %startupFlag, %22 : i1
          }
        }
        sv.ifdef  @FIRRTL_AFTER_INITIAL {
          sv.verbatim "`FIRRTL_AFTER_INITIAL"
        }
      }
    }
    %11 = sv.read_inout %input_ready : !hw.inout<i1>
    %12 = sv.read_inout %output_bits : !hw.inout<i16>
    %13 = sv.read_inout %output_valid : !hw.inout<i1>
    hw.output %11, %13, %12 : i1, i1, i16
  }
  om.class @GCDOM(%basepath: !om.frozenbasepath)  -> (width: !om.integer, useAsyncReset: i1) {
    %0 = om.constant #om.integer<16 : si8> : !om.integer
    %1 = om.constant false
    om.class.fields %0, %1 : !om.integer, i1
  }
  om.class @GCD_Class(%basepath: !om.frozenbasepath)  -> (om: !om.any) {
    %0 = om.object @GCDOM(%basepath) : (!om.frozenbasepath) -> !om.class.type<@GCDOM>
    %1 = om.any_cast %0 : (!om.class.type<@GCDOM>) -> !om.any
    om.class.fields %1 : !om.any
  }
}
