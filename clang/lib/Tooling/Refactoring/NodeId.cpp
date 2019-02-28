//===--- NodeId.cpp - NodeId implementation ---------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/NodeId.h"
#include <atomic>

namespace clang {
namespace tooling {

// For guaranteeing unique ids on NodeId creation.
static size_t nextId() {
  // Start with a relatively high number to avoid bugs if the user mixes
  // explicitly-numbered ids with those generated with `NextId()`. Similarly, we
  // choose a number that allows generated ids to be easily recognized.
  static std::atomic<size_t> Next(2222);
  return Next.fetch_add(1, std::memory_order_relaxed);
}

NodeId::NodeId() : NodeId(nextId()) {}
} // namespace tooling
} // namespace clang
