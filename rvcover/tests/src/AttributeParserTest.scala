// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import ujson.*
import utest.*

def parseJson(filePath: String): Map[String, List[(Boolean, String)]] = {
  val jsonString = os.read(os.Path(filePath))
  val json       = ujson.read(jsonString)

  json.isNull ==> false
  json.obj("instructions").arr.length > 0 ==> true
  json.obj("instructions").arr.head.obj("attributes").arr.length > 0 ==> true

  json.obj("instructions").arr.foldLeft(Map.empty[String, List[(Boolean, String)]]) { (globalAcc, instruction) =>
    val name     = instruction.obj("instructionName").str.replace(".", "_")
    val localMap =
      instruction.obj("attributes").arr.foldLeft(Map.empty[String, List[(Boolean, String)]]) { (acc, attr) =>
        val identifier = attr.obj("identifier").str
        attr.obj.get("value") match {
          case Some(v) =>
            v.str match {
              case "Y"  =>
                acc.updated(identifier, acc.getOrElse(identifier, List()) :+ (true, s"${translateToCamelCase(name)}"))
              case "N"  =>
                acc.updated(identifier, acc.getOrElse(identifier, List()) :+ (false, s"${translateToCamelCase(name)}"))
              case "DC" => acc
              case _    => throw new RuntimeException(s"Unknown value for attribute $identifier: ${v.str}")
            }
          case None    => throw new RuntimeException(s"Attribute $identifier has no value")
        }
      }
    // Merge localMap into globalAcc
    localMap.foldLeft(globalAcc) { case (acc, (k, vList)) =>
      acc.updated(k, acc.getOrElse(k, List()) ++ vList)
    }
  }
}

object AttributeParserTest extends TestSuite:
  val tests = Tests:
    val json = parseJson(s"${sys.env.get("MILL_TEST_RESOURCE_DIR").get}/instruction.json")
    json.empty ==> false
