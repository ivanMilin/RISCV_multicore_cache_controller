<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>20</insertion-point-position>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>&lt;&lt;Target&gt;&gt;::tx</expr>
    <label>&lt;&lt;Target&gt;&gt;::tx</label>
    <wave>
      <expr>chk_ref_model_top.load_from_dmem_flag</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.cache_hit</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.cache_hit_out</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_ref_model_top.state</expr>
    <label/>
    <radix>chk_ref_model_top.state</radix>
  </wave>
  <wave collapsed="true">
    <expr>dmem.data_from_dmem</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.data_from_dmem</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.opcode_in</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>cache_L2.flush</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>bus_ctrl.data_from_L2</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.bus_data_in</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.index_in</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.miss_address[7:2]</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.state</expr>
    <label/>
    <radix>cpu1.controller_and_cache.state</radix>
  </wave>
  <group collapsed="false">
    <expr>cpu1.controller_and_cache.cache_memory_L1[11]</expr>
    <label>cpu1.controller_and_cache.cache_memory_L1[11]</label>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[11].mesi_state</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[11].tag</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cpu1.controller_and_cache.cache_memory_L1[11].data</expr>
      <label/>
      <radix>dec</radix>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>cpu1.controller_and_cache.mask_in</expr>
    <label/>
    <radix/>
  </wave>
</wavelist>
