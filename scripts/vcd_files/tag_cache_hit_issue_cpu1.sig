<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>7</insertion-point-position>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>&lt;embedded&gt;::top.chk_ref_model_top.assert_load_data_from_cpu2_to_cpu1</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>bus_ctrl.cache_hit_out1</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_ref_model_top.clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.bus_address_in[7:2]</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu2.controller_and_cache.index_in[7:2]</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave>
    <expr>cpu1.req_core</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.cache_hit</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.cache_memory_L1[27].data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.cache_memory_L1[34].data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.index_in[7:2]</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.mask_in</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.state</expr>
    <label/>
    <radix>cpu1.controller_and_cache.state</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu2.controller_and_cache.cache_memory_L1[0].data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu2.controller_and_cache.cache_memory_L1[34].data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.opcode_out</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu2.opcode_out</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>cpu2.controller_and_cache.cache_memory_L1[27]</expr>
    <label>cpu2.controller_and_cache.cache_memory_L1[27]</label>
    <wave collapsed="true">
      <expr>cpu2.controller_and_cache.cache_memory_L1[27].mesi_state</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu2.controller_and_cache.cache_memory_L1[27].tag</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu2.controller_and_cache.cache_memory_L1[27].data</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr>cpu1.controller_and_cache.cache_memory_L1[27]</expr>
    <label>cpu1.controller_and_cache.cache_memory_L1[27]</label>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[27].mesi_state</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[27].tag</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[27].data</expr>
      <label/>
      <radix/>
    </wave>
  </group>
</wavelist>
