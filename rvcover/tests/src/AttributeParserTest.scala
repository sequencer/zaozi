// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import ujson.*
import utest.*

def parseJson(filePath: String): Map[String, (List[String], List[String])] = {
  val jsonString = os.read(os.Path(filePath))
  val json       = ujson.read(jsonString)

  json.isNull ==> false
  json.obj("instructions").arr.length > 0 ==> true
  json.obj("instructions").arr.head.obj("attributes").arr.length > 0 ==> true

  // Helper to merge two (List[String], List[String]) tuples
  def mergeTuples(a: (List[String], List[String]), b: (List[String], List[String])): (List[String], List[String]) =
    (a._1 ++ b._1, a._2 ++ b._2)

  json.obj("instructions").arr.foldLeft(Map.empty[String, (List[String], List[String])]) { (globalAcc, instruction) =>
    val name = instruction.obj("instructionName").str.replace(".", "_")
    val camelName = translateToCamelCase(name)

    val localMap = instruction.obj("attributes").arr.foldLeft(Map.empty[String, (List[String], List[String])]) {
      (acc, attr) =>
        val identifier = attr.obj("identifier").str
        attr.obj.get("value") match {
          case Some(v) =>
            v.str match {
              case "Y" =>
                val (yesList, noList) = acc.getOrElse(identifier, (List(), List()))
                acc.updated(identifier, (yesList :+ camelName, noList))
              case "N" =>
                val (yesList, noList) = acc.getOrElse(identifier, (List(), List()))
                acc.updated(identifier, (yesList, noList :+ camelName))
              case "DC" => acc
              case _    => throw new RuntimeException(s"Unknown value for attribute $identifier: ${v.str}")
            }
          case None => throw new RuntimeException(s"Attribute $identifier has no value")
        }
    }

    // Merge localMap into globalAcc
    localMap.foldLeft(globalAcc) { case (acc, (k, vTuple)) =>
      acc.updated(k, mergeTuples(acc.getOrElse(k, (List(), List())), vTuple))
    }
  }
}

object AttributeParserTest extends TestSuite:
  val tests = Tests:
    val json = parseJson(s"${sys.env.get("MILL_TEST_RESOURCE_DIR").get}/instruction.json")
    json.empty ==> false
