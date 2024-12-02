package me.jiuyang.zaozi.internal

import me.jiuyang.zaozi.{Data, Parameter, Wire}
import me.jiuyang.zaozi.circtlib.*

trait Context:
  val handler: CirctHandler
  val root: MlirModule
  val circuitBlock: MlirBlock
  val moduleBlock: MlirBlock
  val currentBlock: MlirBlock
  val interfaceWire: Wire[?]
  val parameter: Parameter
  val elaboratedModule: collection.mutable.ArrayBuffer[String]