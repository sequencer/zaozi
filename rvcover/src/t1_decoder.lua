  fp {

    {
      Seq(
        "isRvD() | rv64D",
        "isRvF() | rv64F",
        "isRvQ() | rv64Q",
        "isRvZfh() | isRv64Zfh() | isRvDZfh() | rvQZfh",
      )
    }

  dp {

    {
      Seq("isRvD() | isRvDZfh() | isRv64D()")
    }

  isBranch {
      Seq("isBne() | isBeq() | isBlt() | isBltu() | isBge() | isBgeu()")
  }

  isJal {

  
      Seq("isJal()")
  }

  isJalr {

  
      Seq("isJalr()")
  }

  rxs2 {

     {
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isHsvW() | isHsvB() | isHfenceVvma() | isHsvH() | isHfenceGvma() | isHsvD() | isOr() | isSrl() | isSltu() | isSra() | isSb() | isAdd() | isXor() | isBeq() | isBge() | isSw() | isBlt() | isBgeu() | isBltu() | isBne() | isSub() | isAnd() | isSlt() | isSh() | isSll() | isAddw() | isSd() | isSllw() | isSraw() | isSubw() | isSrlw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isSfenceVma() | isCzeroNez() | isCzeroEqz()")
      p_vectorReadRs2
    }

  rxs1 {

     {
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFld() | isFcvtDWu() | isFsd() | isFcvtDW() | isFcvtDLu() | isFmvDX() | isFcvtDL() | isFcvtSWu() | isFmvWX() | isFsw() | isFcvtSW() | isFlw() | isFcvtSLu() | isFcvtSL() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isOr() | isSrl() | isOri() | isLhu() | isSltu() | isSra() | isSb() | isLw() | isAdd() | isXor() | isBeq() | isAndi() | isBge() | isSw() | isBlt() | isBgeu() | isSltiu() | isLh() | isBltu() | isJalr() | isBne() | isLbu() | isSub() | isAnd() | isXori() | isSlti() | isSlt() | isAddi() | isLb() | isSh() | isSll() | isSrli() | isSrai() | isSlli() | isLd() | isAddw() | isSd() | isSraiw() | isLwu() | isSllw() | isSraw() | isSubw() | isSrlw() | isAddiw() | isSrliw() | isSlliw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isSfenceVma() | isFsh() | isFlh() | isFcvtHWu() | isFcvtHW() | isFmvHX() | isFcvtHLu() | isFcvtHL() | isCsrrc() | isCsrrs() | isCsrrw() | isCzeroNez() | isCzeroEqz() | isCflushDL1() | isCdiscardDL1()")
      p_vectorReadRs1
    }

  fenceI {

  
      Seq("isFenceI()")
    }

  fence {

  
      Seq("isFence()")
    }

  amo {

    {
      Seq("isRvA() | isRv64A()")_contains(s)
    }

  aluDoubleWords {

        Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFld() | isFsd() | isFsw() | isFlw() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isOr() | isSrl() | isOri() | isLhu() | isSltu() | isSra() | isSb() | isLw() | isAdd() | isXor() | isBeq() | isAndi() | isBge() | isSw() | isBlt() | isBgeu() | isSltiu() | isLh() | isBltu() | isJalr() | isLui() | isBne() | isLbu() | isSub() | isAnd() | isAuipc() | isXori() | isSlti() | isSlt() | isAddi() | isLb() | isJal() | isSh() | isSll() | isSrli() | isSrai() | isSlli() | isLd() | isSd() | isLwu() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isSfenceVma() | isFsh() | isFlh() | isCsrrc() | isCsrrci() | isCsrrs() | isCsrrw() | isCsrrsi() | isCsrrwi() | isCzeroNez() | isCzeroEqz()")
      }
    }

  mem {

    override def default: BitPat = n

        Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFld() | isFsd() | isFsw() | isFlw() | isHsvW() | isHsvB() | isHlvHu() | isHlvB() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHsvD() | isHlvD() | isHlvWu() | isLhu() | isSb() | isLw() | isSw() | isLh() | isLbu() | isLb() | isSh() | isLd() | isSd() | isLwu() | isSfenceVma() | isFsh() | isFlh()")
        Seq("isFenceI()") && fenceIFlushDCache
      }
    }

  rfs1 {

        Seq("isFminD() | isFsgnjD() | isFleD() | isFnmsubD() | isFaddD() | isFcvtWD() | isFmsubD() | isFmulD() | isFcvtWuD() | isFeqD() | isFmaxD() | isFnmaddD() | isFcvtDS() | isFcvtSD() | isFmaddD() | isFsgnjxD() | isFltD() | isFsgnjnD() | isFsubD() | isFsqrtD() | isFclassD() | isFdivD() | isFmvXD() | isFcvtLuD() | isFcvtLD() | isFcvtDH() | isFcvtHD() | isFnmsubS() | isFsgnjxS() | isFmsubS() | isFsgnjnS() | isFdivS() | isFminS() | isFsqrtS() | isFclassS() | isFcvtWuS() | isFmaxS() | isFeqS() | isFleS() | isFmaddS() | isFsgnjS() | isFaddS() | isFltS() | isFmvXW() | isFnmaddS() | isFmulS() | isFcvtWS() | isFsubS() | isFcvtLuS() | isFcvtLS() | isFeqH() | isFsgnjxH() | isFcvtWH() | isFcvtHS() | isFdivH() | isFclassH() | isFsgnjH() | isFmulH() | isFsubH() | isFcvtWuH() | isFaddH() | isFmaxH() | isFsgnjnH() | isFmvXH() | isFcvtSH() | isFmsubH() | isFminH() | isFsqrtH() | isFltH() | isFnmaddH() | isFmaddH() | isFnmsubH() | isFleH() | isFcvtLH() | isFcvtLuH()")
      }
    }

  rfs2 {

        Seq("isFminD() | isFsgnjD() | isFleD() | isFnmsubD() | isFaddD() | isFmsubD() | isFmulD() | isFeqD() | isFmaxD() | isFnmaddD() | isFmaddD() | isFsgnjxD() | isFltD() | isFsgnjnD() | isFsubD() | isFsqrtD() | isFdivD() | isFnmsubS() | isFsgnjxS() | isFmsubS() | isFsgnjnS() | isFdivS() | isFminS() | isFsqrtS() | isFmaxS() | isFeqS() | isFleS() | isFmaddS() | isFsgnjS() | isFaddS() | isFltS() | isFnmaddS() | isFmulS() | isFsubS() | isFeqH() | isFsgnjxH() | isFdivH() | isFsgnjH() | isFmulH() | isFsubH() | isFaddH() | isFmaxH() | isFsgnjnH() | isFmsubH() | isFminH() | isFsqrtH() | isFltH() | isFnmaddH() | isFmaddH() | isFnmsubH() | isFleH()")
      }
    }

  rfs3 {

    ov
        Seq("isFnmsubD() | isFmsubD() | isFnmaddD() | isFmaddD() | isFnmsubS() | isFmsubS() | isFmaddS() | isFnmaddS() | isFmsubH() | isFnmaddH() | isFmaddH() | isFnmsubH()")
      }

  wfd {

  
      Seq("isFminD() | isFsgnjD() | isFnmsubD() | isFaddD() | isFmsubD() | isFld() | isFmulD() | isFmaxD() | isFcvtDWu() | isFnmaddD() | isFcvtDS() | isFcvtSD() | isFmaddD() | isFsgnjxD() | isFsgnjnD() | isFsubD() | isFsqrtD() | isFcvtDW() | isFdivD() | isFcvtDLu() | isFmvDX() | isFcvtDL() | isFcvtDH() | isFcvtHD() | isFnmsubS() | isFsgnjxS() | isFmsubS() | isFsgnjnS() | isFdivS() | isFminS() | isFsqrtS() | isFmaxS() | isFcvtSWu() | isFmvWX() | isFmaddS() | isFsgnjS() | isFaddS() | isFnmaddS() | isFcvtSW() | isFlw() | isFmulS() | isFsubS() | isFcvtSLu() | isFcvtSL() | isFsgnjxH() | isFcvtHS() | isFdivH() | isFsgnjH() | isFmulH() | isFsubH() | isFlh() | isFaddH() | isFmaxH() | isFsgnjnH() | isFcvtSH() | isFcvtHWu() | isFcvtHW() | isFmsubH() | isFminH() | isFsqrtH() | isFnmaddH() | isFmaddH() | isFnmsubH() | isFmvHX() | isFcvtHLu() | isFcvtHL()")
      Seq("isVfmvFS()")
    }

  mul {

  
      Seq("isMulhsu() | isMul() | isMulhu() | isMulh() | isMulw()")
    }

  div {

  
      Seq("isMulhsu() | isMul() | isMulhu() | isMulh() | isMulw()") && !pipelinedMul
      Seq("isRem() | isDiv() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isRemw()")
    }

  wxd {

  
      // TODO: filter out rd
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFleD() | isFcvtWD() | isFcvtWuD() | isFeqD() | isFltD() | isFclassD() | isFmvXD() | isFcvtLuD() | isFcvtLD() | isFclassS() | isFcvtWuS() | isFeqS() | isFleS() | isFltS() | isFmvXW() | isFcvtWS() | isFcvtLuS() | isFcvtLS() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHlvH() | isHlvBu() | isHlvD() | isHlvWu() | isOr() | isSrl() | isOri() | isLhu() | isSltu() | isSra() | isLw() | isAdd() | isXor() | isAndi() | isSltiu() | isLh() | isJalr() | isLui() | isLbu() | isSub() | isAnd() | isAuipc() | isXori() | isSlti() | isSlt() | isAddi() | isLb() | isJal() | isSll() | isSrli() | isSrai() | isSlli() | isLd() | isAddw() | isSraiw() | isLwu() | isSllw() | isSraw() | isSubw() | isSrlw() | isAddiw() | isSrliw() | isSlliw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isFeqH() | isFcvtWH() | isFclassH() | isFcvtWuH() | isFmvXH() | isFltH() | isFleH() | isFcvtLH() | isFcvtLuH() | isCsrrc() | isCsrrci() | isCsrrs() | isCsrrw() | isCsrrsi() | isCsrrwi() | isCzeroNez() | isCzeroEqz()")
      Seq("isVsetvl() | isVsetivli() | isVsetvli() | isVmvXS() | isVcpopM() | isVfirstM()")
    }

  // UOPs

  UOPMEM extends UOP {
    def width = 5

    def xrd: BitPat = encode("isB00000()")

    def xwr: BitPat = encode("isB00001()")

    def pfr: BitPat = encode("isB00010()")

    def pfw: BitPat = encode("isB00011()")

    def xaSwap: BitPat = encode("isB00100()")

    def flushAll: BitPat = encode("isB00101()")

    def xlr: BitPat = encode("isB00110()")

    def xsc: BitPat = encode("isB00111()")

    def xaAdd: BitPat = encode("isB01000()")

    def xaXor: BitPat = encode("isB01001()")

    def xaOr: BitPat = encode("isB01010()")

    def xaAnd: BitPat = encode("isB01011()")

    def xaMin: BitPat = encode("isB01100()")

    def xaMax: BitPat = encode("isB01101()")

    def xaMinu: BitPat = encode("isB01110()")

    def xaMaxu: BitPat = encode("isB01111()")

    // TODO: unused
    def flush: BitPat = encode("isB10000()")

    // TODO: unused
    def pwr: BitPat = encode("isB10001()")

    // TODO: unused
    def produce: BitPat = encode("isB10010()")

    // TODO: unused
    def clean: BitPat = encode("isB10011()")

    def sfence: BitPat = encode("isB10100()")

    def hfencev: BitPat = encode("isB10101()")

    def hfenceg: BitPat = encode("isB10110()")

    def wok: BitPat = encode("isB10111()")

    def hlvx: BitPat = encode("isB10000()")
  }

  memCommand extends UOPDecodeField[RocketDecodePattern] {

        Seq("isFld() | isFlh() | isFlw() | isHlvB() | isHlvBu() | isHlvD() | isHlvH() | isHlvHu() | isHlvW() | isHlvWu() | isLb() | isLbu() | isLd() | isLh() | isLhu() | isLw() | isLwu()") => UOPMEM_xrd
        Seq("isFsd() | isFsh() | isFsw() | isHsvB() | isHsvD() | isHsvH() | isHsvW() | isSb() | isSd() | isSh() | isSw()") => UOPMEM_xwr
        Seq("isAmoswapD() | isAmoswapW()") => UOPMEM_xaSwap
        Seq("isFenceI()") && fenceIFlushDCache => UOPMEM_flushAll
        Seq("isLrD() | isLrW()") => UOPMEM_xlr
        Seq("isScD() | isScW()") => UOPMEM_xsc
        Seq("isAmoaddD() | isAmoaddW()") => UOPMEM_xaAdd
        Seq("isAmoxorD() | isAmoxorW()") => UOPMEM_xaXor
        Seq("isAmoorD() | isAmoorW()") => UOPMEM_xaOr
        Seq("isAmoandD() | isAmoandW()") => UOPMEM_xaAnd
        Seq("isAmominD() | isAmominW()") => UOPMEM_xaMin
        Seq("isAmomaxD() | isAmomaxW()") => UOPMEM_xaMax
        Seq("isAmominuD() | isAmominuW()") => UOPMEM_xaMinu
        Seq("isAmomaxuD() | isAmomaxuW()") => UOPMEM_xaMaxu
        Seq("isSfenceVma()") => UOPMEM_sfence
        Seq("isHfenceVvma()") => UOPMEM_hfencev
        Seq("isHfenceGvma()") => UOPMEM_hfenceg
        Seq("isHlvxHu() | isHlvxWu()") => UOPMEM_hlvx
        UOPMEM_dontCare
      }
    }

    override def uopType: UOPMEM_type = UOPMEM
  }

  UOPCSR extends UOP {
    def width = 3

    def n: BitPat = encode(0)

    def r: BitPat = encode(2)

    def i: BitPat = encode(4)

    def w: BitPat = encode(5)

    def s: BitPat = encode(6)

    def c: BitPat = encode(7)
  }

  csr extends UOPDecodeField[RocketDecodePattern] {

  
      // TODO: default should be N?
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFminD() | isFsgnjD() | isFleD() | isFnmsubD() | isFaddD() | isFcvtWD() | isFmsubD() | isFld() | isFmulD() | isFcvtWuD() | isFeqD() | isFmaxD() | isFcvtDWu() | isFnmaddD() | isFcvtDS() | isFcvtSD() | isFsd() | isFmaddD() | isFsgnjxD() | isFltD() | isFsgnjnD() | isFsubD() | isFsqrtD() | isFclassD() | isFcvtDW() | isFdivD() | isFcvtDLu() | isFmvXD() | isFmvDX() | isFcvtLuD() | isFcvtLD() | isFcvtDL() | isFcvtDH() | isFcvtHD() | isFnmsubS() | isFsgnjxS() | isFmsubS() | isFsgnjnS() | isFdivS() | isFminS() | isFsqrtS() | isFclassS() | isFcvtWuS() | isFmaxS() | isFeqS() | isFcvtSWu() | isFmvWX() | isFleS() | isFmaddS() | isFsgnjS() | isFaddS() | isFsw() | isFltS() | isFmvXW() | isFnmaddS() | isFcvtSW() | isFlw() | isFmulS() | isFcvtWS() | isFsubS() | isFcvtLuS() | isFcvtSLu() | isFcvtLS() | isFcvtSL() | isOr() | isSrl() | isFence() | isOri() | isLhu() | isSltu() | isSra() | isSb() | isLw() | isAdd() | isXor() | isBeq() | isAndi() | isBge() | isSw() | isBlt() | isBgeu() | isSltiu() | isLh() | isBltu() | isJalr() | isLui() | isBne() | isLbu() | isSub() | isAnd() | isAuipc() | isXori() | isSlti() | isSlt() | isAddi() | isLb() | isJal() | isSh() | isSll() | isSrli() | isSrai() | isSlli() | isLd() | isAddw() | isSd() | isSraiw() | isLwu() | isSllw() | isSraw() | isSubw() | isSrlw() | isAddiw() | isSrliw() | isSlliw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isFeqH() | isFsgnjxH() | isFcvtWH() | isFcvtHS() | isFdivH() | isFclassH() | isFsh() | isFsgnjH() | isFmulH() | isFsubH() | isFlh() | isFcvtWuH() | isFaddH() | isFmaxH() | isFsgnjnH() | isFmvXH() | isFcvtSH() | isFcvtHWu() | isFcvtHW() | isFmsubH() | isFminH() | isFsqrtH() | isFltH() | isFnmaddH() | isFmaddH() | isFnmsubH() | isFmvHX() | isFleH() | isFcvtLH() | isFcvtLuH() | isFcvtHLu() | isFcvtHL() | isFenceI() | isCzeroNez() | isCzeroEqz()") => UOPCSR_n
      Seq("isCdiscardDL1() | isCease() | isCflushDL1() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isEbreak() | isEcall() | isSret() | isSfenceVma() | isDret() | isWfi() | isMret() | isMnret()") => UOPCSR_i
      Seq("isCsrrw() | isCsrrwi()") => UOPCSR_w
      Seq("isCsrrs() | isCsrrsi()") => UOPCSR_s
      Seq("isCsrrc() | isCsrrci()") => UOPCSR_c

    override def uopType: UOPCSR_type = UOPCSR
  }

  UOPALU extends UOP {
    def width = 4

    def add: BitPat = encode(0)

    def sl: BitPat = encode(1)

    def seq: BitPat = encode(2)

    def sne: BitPat = encode(3)

    def xor: BitPat = encode(4)

    def sr: BitPat = encode(5)

    def or: BitPat = encode(6)

    def and: BitPat = encode(7)

    def czeqz: BitPat = encode(8)

    def cznez: BitPat = encode(9)

    def sub: BitPat = encode(10)

    def sra: BitPat = encode(11)

    def slt: BitPat = encode(12)

    def sge: BitPat = encode(13)

    def sltu: BitPat = encode(14)

    def sgeu: BitPat = encode(15)

    def div: BitPat = xor

    def divu: BitPat = sr

    def rem: BitPat = or

    def remu: BitPat = and

    def mul: BitPat = add

    def mulh: BitPat = sl

    def mulhsu: BitPat = seq

    def mulhu: BitPat = sne
  }

  aluFn extends UOPDecodeField[RocketDecodePattern] {

     {
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFld() | isFsd() | isFsw() | isFlw() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isLhu() | isSb() | isLw() | isAdd() | isSw() | isLh() | isJalr() | isLui() | isLbu() | isAuipc() | isAddi() | isLb() | isJal() | isSh() | isLd() | isAddw() | isSd() | isLwu() | isAddiw() | isSfenceVma() | isFsh() | isFlh() | isCsrrc() | isCsrrci() | isCsrrs() | isCsrrw() | isCsrrsi() | isCsrrwi() | isCdiscardDL1() | isCflushDL1()") => UOPALU_add
      Seq("isAnd() | isAndi()") => UOPALU_and
      Seq("isOr() | isOri()") => UOPALU_or
      Seq("isBeq()") => UOPALU_seq
      Seq("isBge()") => UOPALU_sge
      Seq("isBgeu()") => UOPALU_sgeu
      Seq("isSll() | isSlli() | isSlli() | isSlliw() | isSllw()") => UOPALU_sl
      Seq("isBlt() | isSlt() | isSlti()") => UOPALU_slt
      Seq("isBltu() | isSltiu() | isSltu()") => UOPALU_sltu
      Seq("isBne()") => UOPALU_sne
      Seq("isSrl() | isSrli() | isSrli() | isSrliw() | isSrlw()") => UOPALU_sr
      Seq("isSra() | isSrai() | isSrai() | isSraiw() | isSraw()") => UOPALU_sra
      Seq("isSub() | isSubw()") => UOPALU_sub
      Seq("isXor() | isXori()") => UOPALU_xor

      // rv_m
      Seq("isMul() | isMulw()") => UOPALU_mul
      Seq("isMulh()") => UOPALU_mulh
      Seq("isMulhu()") => UOPALU_mulhu
      Seq("isMulhsu()") => UOPALU_mulhsu
      Seq("isDiv() | isDivw()") => UOPALU_div
      Seq("isDivu() | isDivuw()") => UOPALU_divu
      Seq("isRem() | isRemw()") => UOPALU_rem
      Seq("isRemu() | isRemuw()") => UOPALU_remu

      Seq("isCzeroEqz()") => UOPALU_czeqz
      Seq("isCzeroNez()") => UOPALU_cznez
      // vector
      // 7_ Vector read RS1 go through ALU rs1 + 0_
      p_vectorReadRs1 => UOPALU_add

    override def uopType: UOPALU_type = UOPALU
  }

  UOPIMM extends UOP {
    def width = 3

    def s: BitPat = encode(0)

    def sb: BitPat = encode(1)

    def u: BitPat = encode(2)

    def uj: BitPat = encode(3)

    def i: BitPat = encode(4)

    def z: BitPat = encode(5)
  }

  selImm extends UOPDecodeField[RocketDecodePattern] {

  
      Seq("isFld() | isFlw() | isHsvW() | isHsvB() | isHsvH() | isHsvD() | isOri() | isLhu() | isLw() | isAndi() | isSltiu() | isLh() | isJalr() | isLbu() | isXori() | isSlti() | isAddi() | isLb() | isSrli() | isSrai() | isSlli() | isLd() | isSraiw() | isLwu() | isAddiw() | isSrliw() | isSlliw() | isFlh()") => UOPIMM_i
      Seq("isFsd() | isFsh() | isFsw() | isSb() | isSd() | isSh() | isSw()") => UOPIMM_s
      Seq("isBeq() | isBge() | isBgeu() | isBlt() | isBltu() | isBne()") => UOPIMM_sb
      Seq("isAuipc() | isLui()") => UOPIMM_u
      Seq("isJal()") => UOPIMM_uj
      Seq("isCsrrci() | isCsrrsi() | isCsrrwi()") => UOPIMM_z

    override def uopType: UOPIMM_type = UOPIMM
  }

  UOPA1 extends UOP {
    def width = 2

    def zero: BitPat = encode(0)

    def rs1: BitPat = encode(1)

    def pc: BitPat = encode(2)
  }

  selAlu1 extends UOPDecodeField[RocketDecodePattern] {

     {
      Seq("isAuipc() | isJal()") => UOPA1_pc
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isFld() | isFcvtDWu() | isFsd() | isFcvtDW() | isFcvtDLu() | isFmvDX() | isFcvtDL() | isFcvtSWu() | isFmvWX() | isFsw() | isFcvtSW() | isFlw() | isFcvtSLu() | isFcvtSL() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isOr() | isSrl() | isOri() | isLhu() | isSltu() | isSra() | isSb() | isLw() | isAdd() | isXor() | isBeq() | isAndi() | isBge() | isSw() | isBlt() | isBgeu() | isSltiu() | isLh() | isBltu() | isJalr() | isBne() | isLbu() | isSub() | isAnd() | isXori() | isSlti() | isSlt() | isAddi() | isLb() | isSh() | isSll() | isSrli() | isSrai() | isSlli() | isLd() | isAddw() | isSd() | isSraiw() | isLwu() | isSllw() | isSraw() | isSubw() | isSrlw() | isAddiw() | isSrliw() | isSlliw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isSfenceVma() | isFsh() | isFlh() | isFcvtHWu() | isFcvtHW() | isFmvHX() | isFcvtHLu() | isFcvtHL() | isCsrrc() | isCsrrs() | isCsrrw() | isCzeroNez() | isCzeroEqz() | isCdiscardDL1() | isCflushDL1()") => UOPA1_rs1
      p_vectorReadRs1 => UOPA1_rs1
      Seq("isCsrrci() | isCsrrsi() | isCsrrwi() | isLui()") => UOPA1_zero

    override def uopType: UOPA1_type = UOPA1
  }

  UOPA2 extends UOP {
    def width = 2

    def zero: BitPat = encode(0)

    def size: BitPat = encode(1)

    def rs2: BitPat = encode(2)

    def imm: BitPat = encode(3)
  }

  selAlu2 extends UOPDecodeField[RocketDecodePattern] {

     {
      Seq("isFld() | isFsd() | isFsw() | isFlw() | isOri() | isLhu() | isSb() | isLw() | isAndi() | isSw() | isSltiu() | isLh() | isJalr() | isLui() | isLbu() | isAuipc() | isXori() | isSlti() | isAddi() | isLb() | isSh() | isSrli() | isSrai() | isSlli() | isLd() | isSd() | isSraiw() | isLwu() | isAddiw() | isSrliw() | isSlliw() | isFsh() | isFlh() | isCsrrci() | isCsrrsi() | isCsrrwi()") => UOPA2_imm
      Seq("isOr() | isSrl() | isSltu() | isSra() | isAdd() | isXor() | isBeq() | isBge() | isBlt() | isBgeu() | isBltu() | isBne() | isSub() | isAnd() | isSlt() | isSll() | isAddw() | isSllw() | isSraw() | isSubw() | isSrlw() | isMulhsu() | isRem() | isDiv() | isMul() | isMulhu() | isMulh() | isRemu() | isDivu() | isRemuw() | isDivw() | isDivuw() | isMulw() | isRemw() | isCzeroNez() | isCzeroEqz()") => UOPA2_rs2
      Seq("isJal()") => UOPA2_size
      Seq("isAmomaxuW() | isAmoandW() | isAmoorW() | isAmoxorW() | isAmoswapW() | isLrW() | isAmomaxW() | isAmoaddW() | isAmominW() | isAmominuW() | isScW() | isLrD() | isAmomaxD() | isAmoswapD() | isAmoxorD() | isAmoandD() | isAmominD() | isAmoorD() | isAmoaddD() | isAmomaxuD() | isAmominuD() | isScD() | isHsvW() | isHsvB() | isHfenceVvma() | isHlvHu() | isHlvxHu() | isHlvB() | isHlvxWu() | isHlvW() | isHsvH() | isHlvH() | isHlvBu() | isHfenceGvma() | isHsvD() | isHlvD() | isHlvWu() | isSfenceVma() | isCsrrc() | isCsrrs() | isCsrrw() | isCdiscardDL1() | isCflushDL1()") => UOPA2_zero
      p_vectorReadRs1 => UOPA2_zero

    override def uopType: UOPA2_type = UOPA2
  }

  vector {
  }

  vectorLSU {
  }

  vectorCSR {
  }

  vectorReadFRs1 {
  }

  // fpu decode
  fldst {

  
      Seq("isFlh() | isFsh() | isFlw() | isFsw() | isFld() | isFsd()")
    }

  fwen {

  
      Seq("isFlh() | isFmvHX() | isFcvtHW() | isFcvtHWu() | isFcvtHL() | isFcvtHLu() | isFcvtSH() | isFcvtHS() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsqrtH() | isFlw() | isFmvWX() | isFcvtSW() | isFcvtSWu() | isFcvtSL() | isFcvtSLu() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsqrtS() | isFld() | isFmvDX() | isFcvtDW() | isFcvtDWu() | isFcvtDL() | isFcvtDLu() | isFcvtSD() | isFcvtDS() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD() | isFsqrtD() | isFcvtHD() | isFcvtDH()")
    }

  fren1 {

     {
      Seq("isFmvXH() | isFclassH() | isFcvtWH() | isFcvtWuH() | isFcvtLH() | isFcvtLuH() | isFcvtSH() | isFcvtHS() | isFeqH() | isFltH() | isFleH() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsqrtH() | isFmvXW() | isFclassS() | isFcvtWS() | isFcvtWuS() | isFcvtLS() | isFcvtLuS() | isFeqS() | isFltS() | isFleS() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsqrtS() | isFmvXD() | isFclassD() | isFcvtWD() | isFcvtWuD() | isFcvtLD() | isFcvtLuD() | isFcvtSD() | isFcvtDS() | isFeqD() | isFltD() | isFleD() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD() | isFsqrtD() | isFcvtHD() | isFcvtDH()")
      p_vectorReadFRegFile
    }

  fren2 {

  
      Seq("isFsh() | isFeqH() | isFltH() | isFleH() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsw() | isFeqS() | isFltS() | isFleS() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsd() | isFeqD() | isFltD() | isFleD() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD()")
    }

  fren3 {

  
      Seq("isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD()")
    }

  fswap12 {

  
      Seq("isFsh() | isFsw() | isFsd()")
    }

  fswap23 {

  
      Seq("isFaddH() | isFsubH() | isFaddS() | isFsubS() | isFaddD() | isFsubD()")
    }

  UOPFType extends UOP {
    val helper = new FPUHelper(minFLen, minFLen, xLen)
    // TODO: wtf here_
    def H = BitPat(helper_H)
    def I = BitPat(helper_I)
    def D = BitPat(helper_D)
    def S = BitPat(helper_S)
    def width = D_getWidth
    def X2 = BitPat_dontCare(width)
  }

  ftypeTagIn extends UOPDecodeField[RocketDecodePattern] {

     {
      Seq("isFsh() | isFmvXH() | isFsw() | isFmvXW() | isFsd() | isFmvXD()") => UOPFType_I
      Seq("isFmvHX() | isFcvtHW() | isFcvtHWu() | isFcvtHL() | isFcvtHLu() | isFclassH() | isFcvtWH() | isFcvtWuH() | isFcvtLH() | isFcvtLuH() | isFcvtSH() | isFeqH() | isFltH() | isFleH() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsqrtH() | isFcvtDH()") => UOPFType_H
      Seq("isFcvtHS() | isFmvWX() | isFcvtSW() | isFcvtSWu() | isFcvtSL() | isFcvtSLu() | isFclassS() | isFcvtWS() | isFcvtWuS() | isFcvtLS() | isFcvtLuS() | isFeqS() | isFltS() | isFleS() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsqrtS() | isFcvtDS()") => UOPFType_S
      Seq("isFmvDX() | isFcvtDW() | isFcvtDWu() | isFcvtDL() | isFcvtDLu() | isFclassD() | isFcvtWD() | isFcvtWuD() | isFcvtLD() | isFcvtLuD() | isFcvtSD() | isFeqD() | isFltD() | isFleD() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD() | isFsqrtD() | isFcvtHD()") => UOPFType_D
       op_vectorReadFRegFile => UOPFType_I
      UOPFType_X2
    }

    override def uopType: UOPFType_type = UOPFType
  }

  ftypeTagOut extends UOPDecodeField[RocketDecodePattern] {

     {
      Seq("isFmvHX() | isFmvWX() | isFmvDX()") => UOPFType_I
      Seq("isFsh() | isFcvtHW() | isFcvtHWu() | isFcvtHL() | isFcvtHLu() | isFmvXH() | isFclassH() | isFcvtHS() | isFeqH() | isFltH() | isFleH() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsqrtH() | isFcvtHD()") => UOPFType_H
      Seq("isFcvtSH() | isFsw() | isFcvtSW() | isFcvtSWu() | isFcvtSL() | isFcvtSLu() | isFmvXW() | isFclassS() | isFeqS() | isFltS() | isFleS() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsqrtS() | isFcvtSD()") => UOPFType_S
      Seq("isFsd() | isFcvtDW() | isFcvtDWu() | isFcvtDL() | isFcvtDLu() | isFmvXD() | isFclassD() | isFcvtDS() | isFeqD() | isFltD() | isFleD() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD() | isFsqrtD() | isFcvtDH()") => UOPFType_D
       op_vectorReadFRegFile => UOPFType_S
      UOPFType_X2
    }

    override def uopType: UOPFType_type = UOPFType
  }

  ffromint {

  
      Seq("isFmvHX() | isFcvtHW() | isFcvtHWu() | isFcvtHL() | isFcvtHLu() | isFmvWX() | isFcvtSW() | isFcvtSWu() | isFcvtSL() | isFcvtSLu() | isFmvDX() | isFcvtDW() | isFcvtDWu() | isFcvtDL() | isFcvtDLu()")
    }

  ftoint {

     {
      Seq("isFsh() | isFmvXH() | isFclassH() | isFcvtWH() | isFcvtWuH() | isFcvtLH() | isFcvtLuH() | isFeqH() | isFltH() | isFleH() | isFsw() | isFmvXW() | isFclassS() | isFcvtWS() | isFcvtWuS() | isFcvtLS() | isFcvtLuS() | isFeqS() | isFltS() | isFleS() | isFsd() | isFmvXD() | isFclassD() | isFcvtWD() | isFcvtWuD() | isFcvtLD() | isFcvtLuD() | isFeqD() | isFltD() | isFleD()")
       op_vectorReadFRegFile
    }

  ffastpipe {

  
      Seq("isFcvtSH() | isFcvtHS() | isFsgnjH() | isFsgnjnH() | isFsgnjxH() | isFminH() | isFmaxH() | isFsgnjS() | isFsgnjnS() | isFsgnjxS() | isFminS() | isFmaxS() | isFcvtSD() | isFcvtDS() | isFsgnjD() | isFsgnjnD() | isFsgnjxD() | isFminD() | isFmaxD() | isFcvtHD() | isFcvtDH()")
    }

  ffma {

  
      Seq("isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD()")
    }

  fdiv {

  
      Seq("isFdivH() | isFdivS() | isFdivD()")
    }

  fsqrt {

  
      Seq("isFsqrtH() | isFsqrtS() | isFsqrtD()")
    }

  fwflags {

  
      Seq("isFcvtHW() | isFcvtHWu() | isFcvtHL() | isFcvtHLu() | isFcvtWH() | isFcvtWuH() | isFcvtLH() | isFcvtLuH() | isFcvtSH() | isFcvtHS() | isFeqH() | isFltH() | isFleH() | isFminH() | isFmaxH() | isFaddH() | isFsubH() | isFmulH() | isFmaddH() | isFmsubH() | isFnmaddH() | isFnmsubH() | isFdivH() | isFsqrtH() | isFcvtSW() | isFcvtSWu() | isFcvtSL() | isFcvtSLu() | isFcvtWS() | isFcvtWuS() | isFcvtLS() | isFcvtLuS() | isFeqS() | isFltS() | isFleS() | isFminS() | isFmaxS() | isFaddS() | isFsubS() | isFmulS() | isFmaddS() | isFmsubS() | isFnmaddS() | isFnmsubS() | isFdivS() | isFsqrtS() | isFcvtDW() | isFcvtDWu() | isFcvtDL() | isFcvtDLu() | isFcvtWD() | isFcvtWuD() | isFcvtLD() | isFcvtLuD() | isFcvtSD() | isFcvtDS() | isFeqD() | isFltD() | isFleD() | isFminD() | isFmaxD() | isFaddD() | isFsubD() | isFmulD() | isFmaddD() | isFmsubD() | isFnmaddD() | isFnmsubD() | isFdivD() | isFsqrtD() | isFcvtHD() | isFcvtDH()")
    }
}

class DecoderInterface(parameter: DecoderParameter) extends Bundle {
  val instruction = Input(UInt(32_W))
  val output = Output(parameter_table_bundle)
}

class FPUDecoderInterface(parameter: DecoderParameter) extends Bundle {
  val instruction = Input(UInt(32_W))
  val output = Output(parameter_floatTable_bundle)
}

/** DecodePattern for an RISC-V instruction */
instruction: Instruction) extends DecodePattern {
  override def bitPat: BitPat = BitPat("b" + instruction_encoding_toString)
  def isVector = instruction_instructionSet_name == "rv_v"
  def isVectorCSR = Seq("isVsetvl() | isVsetivli() | isVsetvli()")_contains(instruction_name)
  def isVectorLSU = instruction_name {
    // unit stride
    // load/store(t) sz element
    ${t}e${sz}_v" if (t == "isL()") || (t == "isS()")                                       => true
    // alias to vl(s)e1_v
    ${t}m_v" if (t == "isL()") || (t == "isS()")                                            => true
    // load/store(t) element w/ first fault
    ${t}e${sz}ff_v" if (t == "isL()") || (t == "isS()")                                     => true
    // load/store(t) r registers with VLEN/sz bytes
    ${tr}re${sz}_v" if tr_startsWith("isL()") || tr_startsWith("isS()")                     => true
    // alias to vl(s)szr_v
    ${tsz}r_v" if tsz_startsWith("isL()") || tsz_startsWith("isS()")                        => true
    // stride
    ${t}se${sz}_v" if (t == "isL()") || (t == "isS()")                                      => true
    // indexed
    ${to}xei${sz}_v" if (to == "lo" || to == "lu" || to == "so" || to == "isSu()")      => true
    false
  }
  def vectorReadFRegFile: Boolean = instruction_name {
    Seq("isVfaddVf() | isVfdivVf() | isVfmaccVf() | isVfmaddVf() | isVfmaxVf() | isVfmergeVfm() | isVfminVf() | isVfmsacVf() | isVfmsubVf() | isVfmulVf() | isVfnmaccVf() | isVfnmaddVf() | isVfnmsacVf() | isVfnmsubVf() | isVfrdivVf() | isVfredusumVs() | isVfrsubVf() | isVfsgnjVf() | isVfsgnjnVf() | isVfsgnjxVf() | isVfsubVf() | isVmfeqVf() | isVmfgeVf() | isVmfgtVf() | isVmfltVf() | isVmfneVf() | isVmfleVf()") => true
    Seq("isVfmvSF() | isVfmvVF()") => true
    Seq("isVfslide1upVf() | isVfslide1downVf()") => true
    false
  }
  // todo: unsure_
  def vectorReadRs1: Boolean = isVectorLSU || (instruction_name {
    // vx type
    ${op}_vx" => true
    ${op}_v_x" => true
    ${op}_wx" => true
    ${op}_vxm" => true
    ${op}_s_x" => true
    // set vl
    setvl${i}" => true
    false
  })
  def vectorReadRs2 = instruction_name {
    // set vl
    setvl" => true
    // stride
    ${t}se${sz}_v" if (t == "isL()") || (t == "isS()") => true
    false
  }
}