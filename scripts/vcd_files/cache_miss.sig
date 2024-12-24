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
    <wave collapsed="true">
      <expr>cache_L2.tag</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>cache_L2.konichiwa</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave>
    <expr>cache_L2.clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.tag</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.cache_hit_out</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.address_to_dmem</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <wave collapsed="true">
    <expr>cache_L2.set_index</expr>
    <label/>
    <radix>dec</radix>
  </wave>
  <group collapsed="false">
    <expr>cache_L2.cache_memory_L2[60]</expr>
    <label>cache_L2.cache_memory_L2[60]</label>
    <group collapsed="false">
      <expr>cache_L2.cache_memory_L2[60][1]</expr>
      <label>cache_L2.cache_memory_L2[60][1]</label>
      <wave>
        <expr>cache_L2.cache_memory_L2[60][1].valid</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>cache_L2.cache_memory_L2[60][1].lru</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>cache_L2.cache_memory_L2[60][1].tag</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>cache_L2.cache_memory_L2[60][1].data</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <group collapsed="false">
      <expr>cache_L2.cache_memory_L2[60][0]</expr>
      <label>cache_L2.cache_memory_L2[60][0]</label>
      <wave>
        <expr>cache_L2.cache_memory_L2[60][0].valid</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>cache_L2.cache_memory_L2[60][0].lru</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>cache_L2.cache_memory_L2[60][0].tag</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>cache_L2.cache_memory_L2[60][0].data</expr>
        <label/>
        <radix/>
      </wave>
    </group>
  </group>
</wavelist>
