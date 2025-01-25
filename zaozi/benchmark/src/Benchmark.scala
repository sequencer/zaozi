// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.benchmark

import java.util.concurrent.TimeUnit
import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra.Blackhole

import me.jiuyang.zaozi.*

// Run with:
// mill zaozi.benchmark.runJmh
class ZaoziBenchmark {

  // This is just an example, copy-paste and modify as appropriate
  // Typically 10 iterations for both warmup and measurement is better
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  @Warmup(iterations = 3)
  @Measurement(iterations = 3)
  @Fork(value = 1)
  @Threads(value = 1)
  def Unit(blackHole: Blackhole) = {}
}