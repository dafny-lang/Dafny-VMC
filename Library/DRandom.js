/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/


let DafnyLibraries = (function() {
  let $module = {};

  $module.DRandom = class DRandom {
    constructor() { }

    Coin() {
      return Boolean(Math.random() < 0.5);
    }
  };
})();