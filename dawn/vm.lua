-- ================================================================
--  vm.lua — Phantom Custom VM  (Level 3)
--
--  IMPORTANT: This file runs on the HOST (standard Lua 5.x / 5.4).
--  Do NOT use Luau-only syntax here (no ~, |, & bitwise ops).
--  Use bit32.bxor / bit32.bor / bit32.band instead.
--
--  Generated VM source strings (which run inside the executor)
--  CAN use Luau syntax — they are emitted as strings, not parsed
--  by the host Lua interpreter.
-- ================================================================

local VM = {}

-- ── Compat: bit32 shim for Lua 5.4 (which dropped bit32) ────────
local _bxor, _bor, _band
if bit32 then
    _bxor = bit32.bxor
    _bor  = bit32.bor
    _band = bit32.band
else
    -- Lua 5.4 native integers — use math to emulate
    _bxor = function(a, b)
        local r, m = 0, 0x80000000
        repeat
            if (a >= m and b < m) or (a < m and b >= m) then r = r + m end
            a = a % m; b = b % m; m = m / 2
        until m < 1
        return r
    end
    _bor  = function(a, b) return _bxor(a, b) + _band(a, b) end
    _band = function(a, b)
        local r, m = 0, 0x80000000
        repeat
            if a >= m and b >= m then r = r + m end
            a = a % m; b = b % m; m = m / 2
        until m < 1
        return r
    end
end

-- ── Opcode definitions (logical names only) ─────────────────────
local OPCODE_DEFS = {
    "LOADNIL", "LOADBOOL", "LOADINT", "LOADFLOAT", "LOADK",
    "MOVE", "GETGLOBAL", "SETGLOBAL", "GETTABLE", "SETTABLE",
    "GETTABLEK", "SETTABLEK", "GETUPVAL", "SETUPVAL",
    "NEWTABLE", "SETLIST",
    "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "IDIV", "ADDK",
    "UNM", "NOT", "LEN",
    "BAND", "BOR", "BXOR", "BNOT", "BSHL", "BSHR",
    "CONCAT",
    "EQ", "LT", "LE", "TEST", "TESTSET", "JMP",
    "CLOSURE", "CALL", "TAILCALL", "RETURN", "VARARG",
    "FORPREP", "FORLOOP", "TFORLOOP", "TFORPREP",
}

-- ── Instruction helpers ───────────────────────────────────────────
local function instr(op, a, b, c)
    return { op = op, a = a or 0, b = b or 0, c = c or 0 }
end
local function instrBx(op, a, bx)
    return { op = op, a = a or 0, bx = bx or 0 }
end
local function instrsBx(op, a, sbx)
    return { op = op, a = a or 0, sbx = sbx or 0 }
end

-- ── VM constructor ────────────────────────────────────────────────
function VM.new(cfg)
    local self    = setmetatable({}, { __index = VM })
    self.cfg      = cfg or {}

    local all_names = {}
    for _, name in ipairs(OPCODE_DEFS) do
        all_names[#all_names + 1] = name
    end

    local dummy_count = self.cfg.dummy_opcodes or 20
    for i = 1, dummy_count do
        all_names[#all_names + 1] = "DUMMY_" .. i
    end

    -- Fisher-Yates shuffle of opcode integer values
    local values = {}
    for i = 0, #all_names - 1 do values[#values + 1] = i end
    for i = #values, 2, -1 do
        local j   = math.random(1, i)
        values[i], values[j] = values[j], values[i]
    end

    self.OP      = {}
    self.OP_NAME = {}
    for i, name in ipairs(all_names) do
        self.OP[name]           = values[i]
        self.OP_NAME[values[i]] = name
    end

    return self
end

-- ── Proto ─────────────────────────────────────────────────────────
function VM.new_proto()
    return {
        code      = {},
        constants = {},
        protos    = {},
        upvals    = {},
        params    = 0,
        is_vararg = false,
        max_stack = 0,
        source    = "?",
    }
end

local function add_const(proto, val)
    for i, k in ipairs(proto.constants) do
        if k == val then return i - 1 end
    end
    proto.constants[#proto.constants + 1] = val
    return #proto.constants - 1
end

-- ── Compiler stub ─────────────────────────────────────────────────
local Compiler = {}
Compiler.__index = Compiler

function Compiler.new(vm_instance)
    return setmetatable({
        vm         = vm_instance,
        OP         = vm_instance.OP,
        reg        = 0,
        high_water = 0,   -- all-time highest reg ever allocated in this frame
        proto      = VM.new_proto(),
        scope      = {},
    }, Compiler)
end

function Compiler:push_scope()
    self.scope[#self.scope + 1] = { locals = {}, reg_start = self.reg }
end

function Compiler:pop_scope()
    local s  = table.remove(self.scope)
    self.reg = s.reg_start
end

function Compiler:alloc_reg(n)
    n = n or 1
    local r  = self.reg
    self.reg = self.reg + n
    if self.reg > self.proto.max_stack then
        self.proto.max_stack = self.reg
    end
    if self.reg > self.high_water then
        self.high_water = self.reg
    end
    return r
end

function Compiler:free_reg(n)
    self.reg = self.reg - (n or 1)
end

function Compiler:emit(...)
    self.proto.code[#self.proto.code + 1] = instr(...)
    return #self.proto.code - 1
end
function Compiler:emitBx(...)
    self.proto.code[#self.proto.code + 1] = instrBx(...)
    return #self.proto.code - 1
end
function Compiler:emitsBx(...)
    self.proto.code[#self.proto.code + 1] = instrsBx(...)
    return #self.proto.code - 1
end

-- Resolve a variable name → register (local) or nil (global/upval)
-- If found in a parent compiler's scope, emits GETUPVAL and returns a fresh reg.
function Compiler:resolve_local(name)
    -- Check own scopes first
    for i = #self.scope, 1, -1 do
        local r = self.scope[i].locals[name]
        if r then return r end
    end
    -- Not a local — check parent compiler chain for upvalue
    if self.parent then
        local parent_reg = self.parent:resolve_local(name)
        if parent_reg then
            -- Register this as an upvalue
            self.upval_refs = self.upval_refs or {}
            -- Check if already registered
            for idx, ref in ipairs(self.upval_refs) do
                if ref.name == name then
                    -- Already have it; emit GETUPVAL and return a fresh reg
                    local r = self:alloc_reg()
                    self:emit(self.OP.GETUPVAL, r, idx - 1, 0)
                    return r
                end
            end
            -- New upvalue
            local uv_idx = #self.upval_refs
            self.upval_refs[uv_idx + 1] = { name = name, instack = true, idx = parent_reg }
            local r = self:alloc_reg()
            self:emit(self.OP.GETUPVAL, r, uv_idx, 0)
            return r
        end
    end
    return nil
end

-- Compile an expression into a register, return the register index.
-- GUARANTEE: after this call, self.reg == returned_register + 1
-- (i.e. exactly one register is live above the watermark).
function Compiler:compile_expr(n)
    if not n then
        local r = self:alloc_reg()
        self:emit(self.OP.LOADNIL, r, 0, 0)
        return r
    end
    local saved = self.reg
    local r = self:compile_node(n)
    if r == nil then
        self.reg = saved
        r = self:alloc_reg()
        self:emit(self.OP.LOADNIL, r, 0, 0)
        return r
    end
    -- Normalise: result must be at exactly `saved`.
    -- Case 1: r < saved  → result is a pre-existing local; copy it down.
    -- Case 2: r == saved → already correct (compile_node allocated it there).
    -- Case 3: r > saved  → compile_node allocated extras and returned a higher reg;
    --                       move result into saved, discard the rest.
    if r ~= saved then
        self:emit(self.OP.MOVE, saved, r, 0)
    end
    self.reg = saved + 1
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end
    return saved
end

function Compiler:compile_expr_to(n, target)
    -- Temporarily set watermark to target so compile_expr places result there
    local old_reg = self.reg
    if target > old_reg then
        -- Need to advance watermark; slots between old_reg and target are reserved
        self.reg = target
    end
    self.reg = target  -- compile_expr uses self.reg as `saved`
    local r = self:compile_expr(n)
    -- r == target guaranteed by compile_expr
    if r ~= target then
        self:emit(self.OP.MOVE, target, r, 0)
    end
    self.reg = target + 1
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end
    return target
end

-- Patch a JMP instruction's sBx to point to current PC
function Compiler:patch_jmp(pc_idx)
    local ins = self.proto.code[pc_idx + 1]
    ins.sbx = #self.proto.code - pc_idx - 1
end

function Compiler:current_pc()
    return #self.proto.code
end

function Compiler:compile_node(node)
    if not node then return end
    local kind = node.kind

    -- ── Block ────────────────────────────────────────────────────
    if kind == "Block" then
        self:push_scope()
        for _, stmt in ipairs(node.stmts or {}) do
            local before = self.reg
            self:compile_node(stmt)
            -- Reclaim temporaries after each statement, but keep locals
            -- (locals are allocated by LocalDecl which updates scope.reg_start indirectly
            --  via alloc_reg, so we only reclaim back to the pre-statement level
            --  if the statement didn't declare new locals)
            if stmt.kind ~= "LocalDecl" and stmt.kind ~= "ForNumeric"
               and stmt.kind ~= "ForGeneric" and stmt.kind ~= "FunctionDecl" then
                self.reg = before
            end
        end
        self:pop_scope()

    -- ── Local declaration ────────────────────────────────────────
    elseif kind == "LocalDecl" then
        local base = self.reg
        local n_names = #node.names
        local values = node.values or {}

        -- Pre-allocate all local slots so compile_expr_to cannot overwrite them
        self.reg = base + n_names
        if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end

        for i = 1, n_names do
            local r = base + i - 1
            if values[i] then
                -- Temporarily set reg to r so compile_expr_to targets it correctly
                self.reg = r
                self:compile_expr_to(values[i], r)
                -- compile_expr_to sets self.reg = r+1; restore to full locals width
                self.reg = base + n_names
            else
                self:emit(self.OP.LOADNIL, r, 0, 0)
            end
        end

        -- Register names in scope
        local scope = self.scope[#self.scope]
        for i, name in ipairs(node.names) do
            scope.locals[name] = base + i - 1
        end

    -- ── Assignment ───────────────────────────────────────────────
    elseif kind == "Assignment" then
        local targets = node.targets
        local values  = node.values or {}
        local saved_base = self.reg  -- all temps are freed after each assignment

        for i, target in ipairs(targets) do
            self.reg = saved_base  -- reset for each target
            local val_reg
            if values[i] then
                val_reg = self:compile_expr(values[i])
            else
                val_reg = self:alloc_reg()
                self:emit(self.OP.LOADNIL, val_reg, 0, 0)
            end
            -- val_reg == saved_base now (compile_expr guarantee)

            if target.kind == "NameRef" then
                local lr = self:resolve_local(target.name)
                if lr then
                    if val_reg ~= lr then
                        self:emit(self.OP.MOVE, lr, val_reg, 0)
                    end
                else
                    local ki = add_const(self.proto, target.name)
                    self:emitBx(self.OP.SETGLOBAL, val_reg, ki)
                end
            elseif target.kind == "DotIndex" then
                -- val is at saved_base; compile obj into saved_base+1
                self.reg = saved_base + 1
                local obj_r = self:compile_expr(target.object)
                local ki = add_const(self.proto, target.name)
                local kr = self:alloc_reg()
                self:emitBx(self.OP.LOADK, kr, ki)
                self:emit(self.OP.SETTABLE, obj_r, kr, val_reg)
            elseif target.kind == "BracketIndex" then
                self.reg = saved_base + 1
                local obj_r = self:compile_expr(target.object)
                local idx_r = self:compile_expr(target.index)
                self:emit(self.OP.SETTABLE, obj_r, idx_r, val_reg)
            end
        end
        self.reg = saved_base  -- free all temps

    -- ── If statement ─────────────────────────────────────────────
    elseif kind == "If" then
        local cond_base = self.reg
        local cond_r = self:compile_expr(node.cond)
        self:emit(self.OP.TEST, cond_r, 0, 0)
        self.reg = cond_base  -- free cond temp
        local jmp_over_body = self:emitsBx(self.OP.JMP, 0, 0)

        self:compile_node(node.body)

        local exit_jmps = {}
        exit_jmps[#exit_jmps + 1] = self:emitsBx(self.OP.JMP, 0, 0)
        self:patch_jmp(jmp_over_body)

        for _, ei in ipairs(node.elseifs or {}) do
            local cr = self:compile_expr(ei.cond)
            self:emit(self.OP.TEST, cr, 0, 0)
            self.reg = cond_base
            local jmp_ei = self:emitsBx(self.OP.JMP, 0, 0)
            self:compile_node(ei.body)
            exit_jmps[#exit_jmps + 1] = self:emitsBx(self.OP.JMP, 0, 0)
            self:patch_jmp(jmp_ei)
        end

        if node.elsebody then
            self:compile_node(node.elsebody)
        end

        for _, j in ipairs(exit_jmps) do
            self:patch_jmp(j)
        end

    -- ── While loop ───────────────────────────────────────────────
    elseif kind == "While" then
        local cond_base = self.reg
        local loop_start = self:current_pc()
        local cond_r = self:compile_expr(node.cond)
        self:emit(self.OP.TEST, cond_r, 0, 0)
        self.reg = cond_base
        local jmp_exit = self:emitsBx(self.OP.JMP, 0, 0)
        self:compile_node(node.body)
        local back = loop_start - self:current_pc() - 1
        self:emitsBx(self.OP.JMP, 0, back)
        self:patch_jmp(jmp_exit)

    -- ── Repeat/until ─────────────────────────────────────────────
    elseif kind == "Repeat" then
        local cond_base = self.reg
        local loop_start = self:current_pc()
        self:compile_node(node.body)
        local cond_r = self:compile_expr(node.cond)
        self:emit(self.OP.TEST, cond_r, 0, 1)
        self.reg = cond_base
        local back = loop_start - self:current_pc() - 1
        self:emitsBx(self.OP.JMP, 0, back)

    -- ── Numeric for ──────────────────────────────────────────────
    elseif kind == "ForNumeric" then
        self:push_scope()
        local base = self:alloc_reg(4) -- init, limit, step, var
        self:compile_expr_to(node.start, base)
        self:compile_expr_to(node.stop, base + 1)
        if node.step then
            self:compile_expr_to(node.step, base + 2)
        else
            self:emitBx(self.OP.LOADINT, base + 2, 1)
        end
        local scope = self.scope[#self.scope]
        scope.locals[node.var] = base + 3

        local prep = self:emitsBx(self.OP.FORPREP, base, 0)
        self:compile_node(node.body)
        local loop = self:emitsBx(self.OP.FORLOOP, base, 0)
        -- patch: FORPREP jumps to FORLOOP, FORLOOP jumps back to body start
        self.proto.code[prep + 1].sbx = loop - prep - 1
        self.proto.code[loop + 1].sbx = prep - loop
        self:pop_scope()

    -- ── Generic for ──────────────────────────────────────────────
    elseif kind == "ForGeneric" then
        self:push_scope()
        local base = self:alloc_reg(3) -- iterator, state, control
        -- compile iterators
        local iters = node.iterators or {}
        if #iters == 1 and (iters[1].kind == "Call" or iters[1].kind == "MethodCall") then
            -- Single call (e.g. pairs(t), ipairs(t)) — capture 3 return values
            local call_node = iters[1]
            local func_r, n_args
            if call_node.kind == "Call" then
                func_r = self:compile_expr(call_node.func)
                n_args = #(call_node.args or {})
                if func_r ~= base then
                    self:emit(self.OP.MOVE, base, func_r, 0)
                end
                for i, arg in ipairs(call_node.args or {}) do
                    local target = base + i
                    local r = self:compile_expr(arg)
                    if r ~= target then
                        if self.reg <= target then self.reg = target + 1 end
                        self:emit(self.OP.MOVE, target, r, 0)
                    end
                end
            else -- MethodCall
                local obj_r = self:compile_expr(call_node.object)
                local ki = add_const(self.proto, call_node.method)
                local kr = self:alloc_reg()
                self:emitBx(self.OP.LOADK, kr, ki)
                self:emit(self.OP.GETTABLE, base, obj_r, kr) -- base = obj[method]
                self:free_reg(1)
                local sr = self:alloc_reg()
                self:emit(self.OP.MOVE, sr, obj_r, 0) -- self arg at base+1
                n_args = #(call_node.args or {})
                for i, arg in ipairs(call_node.args or {}) do
                    local target = base + 1 + i
                    local r = self:compile_expr(arg)
                    if r ~= target then
                        if self.reg <= target then self.reg = target + 1 end
                        self:emit(self.OP.MOVE, target, r, 0)
                    end
                end
                n_args = n_args + 1 -- +1 for self
            end
            if self.reg <= base + n_args then self.reg = base + n_args + 1 end
            self:emit(self.OP.CALL, base, n_args + 1, 4) -- C=4: capture 3 return values
            self.reg = base + 3
        else
            for idx, iter in ipairs(iters) do
                if idx <= 3 then
                    self:compile_expr_to(iter, base + idx - 1)
                end
            end
        end
        -- allocate loop vars
        local n_vars = #node.vars
        local var_base = self:alloc_reg(n_vars)
        local scope = self.scope[#self.scope]
        for i, name in ipairs(node.vars) do
            scope.locals[name] = var_base + i - 1
        end

        local jmp_in = self:emitsBx(self.OP.JMP, 0, 0)
        local body_start = self:current_pc()
        self:compile_node(node.body)
        self:patch_jmp(jmp_in)
        -- TFORLOOP: call iterator, assign vars, jump back if non-nil
        self:emit(self.OP.TFORLOOP, base, 0, n_vars)
        local back = body_start - self:current_pc() - 1
        self:emitsBx(self.OP.JMP, 0, back)
        self:pop_scope()

    -- ── Do block ─────────────────────────────────────────────────
    elseif kind == "Do" then
        self:compile_node(node.body)

    -- ── Return ───────────────────────────────────────────────────
    elseif kind == "Return" then
        local values = node.values or {}
        if #values == 0 then
            self:emit(self.OP.RETURN, 0, 1, 0)
        else
            local base = self.reg
            for i, v in ipairs(values) do
                self:compile_expr_to(v, base + i - 1)
            end
            self:emit(self.OP.RETURN, base, #values + 1, 0)
        end

    -- ── Break / Continue ─────────────────────────────────────────
    elseif kind == "Break" or kind == "Continue" then
        -- Emit a JMP placeholder — patching loops properly requires
        -- a break/continue list. For now emit a forward JMP that
        -- the interpreter handles via pcall-style unwind.
        self:emitsBx(self.OP.JMP, 0, 0)

    -- ── Function declarations ────────────────────────────────────
    elseif kind == "FunctionDecl" then
        local saved_reg = self.reg
        local fr = self:compile_function(node)
        local name = node.name

        if not name:find("[.:]") then
            -- Simple global: function foo() end  →  SETGLOBAL
            local lr = self:resolve_local(name)
            if lr then
                self:emit(self.OP.MOVE, lr, fr, 0)
            else
                local ki = add_const(self.proto, name)
                self:emitBx(self.OP.SETGLOBAL, fr, ki)
            end
        else
            -- Dotted/colon: function a.b.c() end
            -- Split on dots and colons, walk the chain, SETTABLE the last key.
            local parts = {}
            for part in name:gmatch("[^.:]+") do
                parts[#parts + 1] = part
            end

            -- Resolve root object: use local register directly (no copy needed —
            -- SETTABLE on a local register mutates the same underlying table).
            -- For globals, load into a scratch register above fr.
            local obj_r
            local root_local = self:resolve_local(parts[1])
            if root_local then
                obj_r = root_local
            else
                local scratch = self.reg
                local ki = add_const(self.proto, parts[1])
                self:emitBx(self.OP.GETGLOBAL, scratch, ki)
                self.reg = scratch + 1
                if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end
                obj_r = scratch
            end

            -- Walk intermediate parts (all but last) via GETTABLE into a scratch
            for i = 2, #parts - 1 do
                local scratch = self.reg
                local ki = add_const(self.proto, parts[i])
                local kr = self:alloc_reg()
                self:emitBx(self.OP.LOADK, kr, ki)
                self:emit(self.OP.GETTABLE, scratch, obj_r, kr)
                self.reg = scratch + 1
                if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end
                obj_r = scratch
            end

            -- SETTABLE: obj_r[last_key] = fr
            local last_ki = add_const(self.proto, parts[#parts])
            local kr = self:alloc_reg()
            self:emitBx(self.OP.LOADK, kr, last_ki)
            self:emit(self.OP.SETTABLE, obj_r, kr, fr)
        end
        -- Free the closure register and any scratch: FunctionDecl is a statement,
        -- its temporary registers should not permanently inflate the watermark.
        self.reg = saved_reg

    elseif kind == "LocalFunction" then
        local scope = self.scope[#self.scope]
        local fr = self:compile_function(node)
        scope.locals[node.name] = fr

    -- ── Expressions ──────────────────────────────────────────────

    elseif kind == "NumberLit" then
        local r = self:alloc_reg()
        local int = math.floor(node.value)
        if int == node.value and int >= -65536 and int <= 65535 then
            self:emitBx(self.OP.LOADINT, r, int)
        else
            local ki = add_const(self.proto, node.value)
            self:emitBx(self.OP.LOADK, r, ki)
        end
        return r

    elseif kind == "StringLit" then
        local r  = self:alloc_reg()
        local ki = add_const(self.proto, node.value)
        self:emitBx(self.OP.LOADK, r, ki)
        return r

    elseif kind == "BoolLit" then
        local r = self:alloc_reg()
        self:emit(self.OP.LOADBOOL, r, node.value and 1 or 0, 0)
        return r

    elseif kind == "NilLit" then
        local r = self:alloc_reg()
        self:emit(self.OP.LOADNIL, r, 0, 0)
        return r

    elseif kind == "Vararg" then
        local r = self:alloc_reg()
        self:emit(self.OP.VARARG, r, 2, 0)
        return r

    elseif kind == "NameRef" then
        local lr = self:resolve_local(node.name)
        if lr then return lr end
        local r  = self:alloc_reg()
        local ki = add_const(self.proto, node.name)
        self:emitBx(self.OP.GETGLOBAL, r, ki)
        return r

    elseif kind == "DotIndex" then
        -- After compile_expr, obj_r == self.reg - 1 == saved.
        -- We need: LOADK kr=key, GETTABLE result=obj[key]
        -- Result can reuse obj slot ONLY if VM reads B before writing A.
        -- To be safe: allocate a fresh result reg, then rewind to obj slot.
        local obj_r = self:compile_expr(node.object)  -- obj_r == saved
        local kr = self:alloc_reg()                   -- kr == saved+1
        local ki = add_const(self.proto, node.name)
        self:emitBx(self.OP.LOADK, kr, ki)
        -- Result goes into obj_r (safe: GETTABLE reads stack[B] and stack[C]
        -- before writing stack[A]; A==B is well-defined in the VM handler
        -- because it does: stack[a] = stack[b][stack[c]])
        self:emit(self.OP.GETTABLE, obj_r, obj_r, kr)
        -- kr is dead; rewind to obj_r+1
        self.reg = obj_r + 1
        return obj_r

    elseif kind == "BracketIndex" then
        local obj_r = self:compile_expr(node.object)   -- obj_r == saved
        local idx_r = self:compile_expr(node.index)    -- idx_r == saved+1
        -- Result into obj_r (same safe self-overwrite as DotIndex)
        self:emit(self.OP.GETTABLE, obj_r, obj_r, idx_r)
        self.reg = obj_r + 1
        return obj_r

    elseif kind == "BinOp" then
        return self:compile_binop(node)

    elseif kind == "UnOp" then
        return self:compile_unop(node)

    elseif kind == "TableConstructor" then
        return self:compile_table(node)

    elseif kind == "Call" then
        local saved = self.reg
        local r = self:compile_call(node)
        -- When used as a statement the result is discarded; free the result
        -- register so it doesn't permanently inflate the watermark and
        -- collide with live locals (e.g. overwriting GameDetector's slot).
        if self.reg == r + 1 then self.reg = saved end
        return r

    elseif kind == "MethodCall" then
        local saved = self.reg
        local r = self:compile_method_call(node)
        if self.reg == r + 1 then self.reg = saved end
        return r

    elseif kind == "Lambda" then
        return self:compile_function(node)

    -- ── Goto / Label (emit as no-ops for now) ────────────────────
    elseif kind == "Goto" or kind == "Label" then
        -- no-op
    end
end

-- ── Binary operations ────────────────────────────────────────────

local ARITH_OPS = {
    ["+"] = "ADD", ["-"] = "SUB", ["*"] = "MUL", ["/"] = "DIV",
    ["%"] = "MOD", ["^"] = "POW", ["//"] = "IDIV",
}

function Compiler:compile_binop(node)
    local op = node.op

    -- Arithmetic
    if ARITH_OPS[op] then
        local lr = self:compile_expr(node.left)
        local rr = self:compile_expr(node.right)
        -- lr is at reg-2, rr at reg-1; result goes into lr slot, rr slot freed
        local r = lr
        self:emit(self.OP[ARITH_OPS[op]], r, lr, rr)
        self.reg = r + 1
        return r
    end

    -- String concat — flatten the entire .. chain to avoid O(n) register depth.
    -- a..b..c..d parses as ((a..b)..c)..d; we walk left spines to collect all
    -- operands, compile them into consecutive registers, then emit one CONCAT.
    if op == ".." then
        local operands = {}
        local function collect(n)
            if n.kind == "BinOp" and n.op == ".." then
                collect(n.left)
                operands[#operands + 1] = n.right
            else
                operands[#operands + 1] = n
            end
        end
        collect(node.left)
        operands[#operands + 1] = node.right

        local base = self.reg
        for i, operand in ipairs(operands) do
            self:compile_expr_to(operand, base + i - 1)
        end
        local last = base + #operands - 1
        self:emit(self.OP.CONCAT, base, base, last)
        self.reg = base + 1
        return base
    end

    -- Comparison
    if op == "==" or op == "~=" or op == "<" or op == ">" or op == "<=" or op == ">=" then
        local lr = self:compile_expr(node.left)
        local rr = self:compile_expr(node.right)
        -- result boolean goes into lr slot
        local r = lr

        local cmp_op, a_val
        if op == "==" then     cmp_op = "EQ"; a_val = 1
        elseif op == "~=" then cmp_op = "EQ"; a_val = 0
        elseif op == "<" then  cmp_op = "LT"; a_val = 1
        elseif op == ">" then  cmp_op = "LT"; a_val = 1; lr, rr = rr, lr
        elseif op == "<=" then cmp_op = "LE"; a_val = 1
        elseif op == ">=" then cmp_op = "LE"; a_val = 1; lr, rr = rr, lr
        end

        self:emit(self.OP[cmp_op], a_val, lr, rr)
        self:emitsBx(self.OP.JMP, 0, 1)
        self:emit(self.OP.LOADBOOL, r, 0, 1)
        self:emit(self.OP.LOADBOOL, r, 1, 0)
        self.reg = r + 1
        return r
    end

    -- and / or (short-circuit)
    if op == "and" then
        local lr = self:compile_expr(node.left)
        local r = lr  -- result in lr's slot
        self:emit(self.OP.TEST, r, 0, 0)
        local jmp = self:emitsBx(self.OP.JMP, 0, 0)
        -- right side compiled into same slot (reg == r+1 after lr was set above... no)
        -- We need rr in a fresh reg, then move to r
        local rr = self:compile_expr(node.right)
        self:emit(self.OP.MOVE, r, rr, 0)
        self.reg = r + 1
        self:patch_jmp(jmp)
        return r
    end

    if op == "or" then
        local lr = self:compile_expr(node.left)
        local r = lr
        self:emit(self.OP.TEST, r, 0, 1)
        local jmp = self:emitsBx(self.OP.JMP, 0, 0)
        local rr = self:compile_expr(node.right)
        self:emit(self.OP.MOVE, r, rr, 0)
        self.reg = r + 1
        self:patch_jmp(jmp)
        return r
    end

    -- Bitwise
    local BIT_OPS = { ["&"] = "BAND", ["|"] = "BOR", ["~"] = "BXOR", ["<<"] = "BSHL", [">>"] = "BSHR" }
    if BIT_OPS[op] then
        local lr = self:compile_expr(node.left)
        local rr = self:compile_expr(node.right)
        local r = lr
        self:emit(self.OP[BIT_OPS[op]], r, lr, rr)
        self.reg = r + 1
        return r
    end

    error("[Compiler] Unknown binop: " .. tostring(op))
end

-- ── Unary operations ─────────────────────────────────────────────

function Compiler:compile_unop(node)
    local or_reg = self:compile_expr(node.operand)
    local r = or_reg  -- overwrite operand slot with result
    if node.op == "-" then
        self:emit(self.OP.UNM, r, or_reg, 0)
    elseif node.op == "not" then
        self:emit(self.OP.NOT, r, or_reg, 0)
    elseif node.op == "#" then
        self:emit(self.OP.LEN, r, or_reg, 0)
    end
    self.reg = r + 1
    return r
end

-- ── Table constructor ────────────────────────────────────────────

function Compiler:compile_table(node)
    local r = self:alloc_reg()
    self:emit(self.OP.NEWTABLE, r, 0, 0)
    local array_idx = 0
    for _, field in ipairs(node.fields or {}) do
        local scratch = r + 1
        self.reg = scratch  -- reset scratch area for each field
        if field.kind == "NameField" then
            local ki = add_const(self.proto, field.name)
            local kr = self:alloc_reg()     -- r+1
            self:emitBx(self.OP.LOADK, kr, ki)
            local vr = self:compile_expr(field.value)  -- r+2
            self:emit(self.OP.SETTABLE, r, kr, vr)
        elseif field.kind == "IndexField" then
            local kr = self:compile_expr(field.key)    -- r+1
            local vr = self:compile_expr(field.value)  -- r+2
            self:emit(self.OP.SETTABLE, r, kr, vr)
        elseif field.kind == "ValueField" then
            array_idx = array_idx + 1
            local vr  = self:compile_expr(field.value)  -- r+1
            local idx = self:alloc_reg()                -- r+2
            self:emitBx(self.OP.LOADINT, idx, array_idx)
            self:emit(self.OP.SETTABLE, r, idx, vr)
        end
        -- rewind scratch and max_stack — field temps are not permanent allocations
        self.reg = scratch
        if self.proto.max_stack > scratch then self.proto.max_stack = scratch end
    end
    self.reg = r + 1
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end
    return r
end

-- ── Function call ────────────────────────────────────────────────

function Compiler:compile_call(node)
    local base = self.reg
    local n_args = #(node.args or {})
    -- Reserve the entire call frame up front
    local frame_top = base + 1 + n_args
    self.reg = frame_top
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end

    -- Compile function into scratch above frame, move into base
    local scratch = frame_top
    self.reg = scratch
    local func_r = self:compile_expr(node.func)  -- lands at scratch
    self:emit(self.OP.MOVE, base, func_r, 0)

    -- Compile each argument into scratch, move into slot
    for i, arg in ipairs(node.args or {}) do
        local arg_slot = base + i
        self.reg = frame_top
        local ar = self:compile_expr(arg)
        if ar ~= arg_slot then
            self:emit(self.OP.MOVE, arg_slot, ar, 0)
        end
    end

    self.reg = frame_top
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end

    self:emit(self.OP.CALL, base, n_args + 1, 2)
    self.reg = base + 1
    return base
end

-- ── Method call ──────────────────────────────────────────────────

function Compiler:compile_method_call(node)
    -- Frame layout: [base]=fn, [base+1]=self, [base+2..base+1+n_args]=args
    local base = self.reg
    local n_args = #(node.args or {})
    -- Reserve the entire call frame up front so no sub-expression can steal it
    local frame_top = base + 2 + n_args
    self.reg = frame_top
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end

    -- Compile the object expression into a scratch register ABOVE the frame,
    -- then move it into the self slot (base+1). This prevents the object
    -- expression from seeing base as a free register and corrupting the frame.
    local scratch = frame_top
    self.reg = scratch
    local obj_r = self:compile_expr(node.object)  -- lands at scratch
    -- obj_r == scratch; copy into self slot
    self:emit(self.OP.MOVE, base + 1, obj_r, 0)

    -- Look up method: use scratch as temp key reg (obj_r already consumed)
    local ki = add_const(self.proto, node.method)
    self:emitBx(self.OP.LOADK, scratch, ki)
    self:emit(self.OP.GETTABLE, base, base + 1, scratch)
    -- scratch (key) is dead now; restore reg to frame_top for arg compilation
    self.reg = frame_top

    -- Compile arguments into base+2 .. base+1+n_args
    -- Each arg gets its own scratch above frame_top, then moved into place
    for i, arg in ipairs(node.args or {}) do
        local arg_slot = base + 1 + i  -- base+2 for i=1, etc.
        self.reg = frame_top
        local ar = self:compile_expr(arg)
        if ar ~= arg_slot then
            self:emit(self.OP.MOVE, arg_slot, ar, 0)
        end
    end

    -- Restore reg to frame_top before CALL (max_stack already accounts for it)
    self.reg = frame_top
    if self.reg > self.proto.max_stack then self.proto.max_stack = self.reg end

    -- b = n_args+2: counts fn slot + self slot + args
    self:emit(self.OP.CALL, base, n_args + 2, 2)
    self.reg = base + 1
    return base
end

-- ── Compile function body into a sub-proto ───────────────────────

function Compiler:compile_function(node)
    local parent_compiler = self
    local child = Compiler.new(self.vm)
    child.proto.params = #(node.params or {})
    child.proto.is_vararg = node.is_vararg or false

    child:push_scope()
    local scope = child.scope[#child.scope]
    for i, pname in ipairs(node.params or {}) do
        local pr = child:alloc_reg()
        scope.locals[pname] = pr
    end

    -- Give the child a reference to the parent so it can resolve upvalues
    child.parent = parent_compiler

    -- Compile body statements
    if node.body and node.body.stmts then
        for _, stmt in ipairs(node.body.stmts) do
            child:compile_node(stmt)
        end
    end
    child:pop_scope()

    local proto = child:finalize()

    -- Populate upvals descriptors: for every upvalue the child referenced,
    -- record whether it's in the parent's stack (instack=true) or an outer upval.
    -- child.upval_refs is built by resolve_upvalue during child compilation.
    proto.upvals = proto.upvals or {}
    if child.upval_refs then
        for idx, ref in ipairs(child.upval_refs) do
            proto.upvals[idx] = ref
        end
    end

    parent_compiler.proto.protos[#parent_compiler.proto.protos + 1] = proto
    local proto_idx = #parent_compiler.proto.protos - 1

    local r = self:alloc_reg()
    self:emitBx(self.OP.CLOSURE, r, proto_idx)
    return r
end

function Compiler:finalize()
    local last = self.proto.code[#self.proto.code]
    if not last or last.op ~= self.OP.RETURN then
        self:emit(self.OP.RETURN, 0, 1, 0)
    end
    return self.proto
end

-- ── Bytecode serializer ───────────────────────────────────────────
local CHUNK = 200 -- max args per string.char() to stay under 255 register limit

local function chunked_string_char(s)
    local chunks = {}
    local i = 1
    while i <= #s do
        local b = {}
        for j = i, math.min(i + CHUNK - 1, #s) do
            b[#b + 1] = tostring(s:byte(j))
        end
        chunks[#chunks + 1] = "string.char(" .. table.concat(b, ",") .. ")"
        i = i + CHUNK
    end
    if #chunks == 0 then return '""' end
    return table.concat(chunks, "..")
end

local function serialize_value(v)
    local t = type(v)
    if t == "number" then
        -- Use full precision format to preserve large integers exactly
        local int = math.floor(v)
        if int == v and int >= -2^53 and int <= 2^53 then
            return string.format("%.0f", v)
        end
        return string.format("%.17g", v)
    elseif t == "string" then
        return chunked_string_char(v)
    elseif t == "boolean" then
        return tostring(v)
    else
        return "nil"
    end
end

local function serialize_instr(ins)
    local parts = { string.format("{op=%d,a=%d", ins.op, ins.a or 0) }
    if ins.b   ~= nil then parts[#parts + 1] = string.format(",b=%d",   ins.b)   end
    if ins.c   ~= nil then parts[#parts + 1] = string.format(",c=%d",   ins.c)   end
    if ins.bx  ~= nil then parts[#parts + 1] = string.format(",bx=%d",  ins.bx)  end
    if ins.sbx ~= nil then parts[#parts + 1] = string.format(",sbx=%d", ins.sbx) end
    return table.concat(parts) .. "}"
end

local function serialize_proto(proto)
    local code_parts = {}
    for _, ins in ipairs(proto.code) do
        code_parts[#code_parts + 1] = serialize_instr(ins)
    end

    local k_parts = {}
    for _, k in ipairs(proto.constants) do
        k_parts[#k_parts + 1] = serialize_value(k)
    end

    local p_parts = {}
    for _, p in ipairs(proto.protos) do
        p_parts[#p_parts + 1] = serialize_proto(p)
    end

    -- Serialize upvalue descriptors so CLOSURE can wire them up
    local uv_parts = {}
    for _, uv in ipairs(proto.upvals or {}) do
        uv_parts[#uv_parts + 1] = string.format(
            "{instack=%s,idx=%d,name=%q}",
            tostring(uv.instack), uv.idx or 0, uv.name or ""
        )
    end

    return table.concat({
        "{",
        "code={" .. table.concat(code_parts, ",") .. "},",
        "constants={" .. table.concat(k_parts, ",") .. "},",
        "protos={" .. table.concat(p_parts, ",") .. "},",
        "upvals={" .. table.concat(uv_parts, ",") .. "},",
        string.format("params=%d,max_stack=%d", proto.params or 0, proto.max_stack or 8),
        "}",
    }, "\n")
end

-- ── Interpreter source builder ────────────────────────────────────
-- Emits Lua SOURCE CODE (as a string) that will run inside the
-- executor. The generated code uses Luau syntax (~, |, &) because
-- it will be executed by the Roblox executor, not host Lua.
-- Host Lua only sees these as string literals — never parses them.

function VM:build_interpreter_source(proto_str, cfg, namegen)
    local OP = self.OP or error("OP table required for interpreter source building")
    local ng = namegen or error("Name generator required for interpreter source building")

    -- ── Generate ALL reserved names FIRST, before any handler bodies ──
    -- This ensures dummy template ng:generate() calls (which run later)
    -- cannot produce names that collide with these already-reserved ones.
    local n_unpack      = ng:generate()
    local n_getfenv     = ng:generate()
    local n_select      = ng:generate()
    local n_type        = ng:generate()
    local n_pcall       = ng:generate()
    local n_hash        = ng:generate() or error("Name generator failed to produce a name")
    local n_guard       = ng:generate()
    local n_tick        = ng:generate()
    -- Loop vars for the dispatch-table merge loops (emitted as source identifiers)
    local lv1, lv2      = ng:generate(), ng:generate()
    local lv3, lv4      = ng:generate(), ng:generate()
    -- Sub-table names for the split dispatch
    local n_da          = ng:generate()
    local n_db          = ng:generate()
    -- Fake hash-guard internals
    local n_proto_guard = ng:generate()
    local fh_accum      = ng:generate()
    local fh_iter       = ng:generate()

    local N = {
        execute  = ng:generate(),
        stack    = ng:generate(),
        pc       = ng:generate(),
        proto    = ng:generate(),
        upvals   = ng:generate(),
        env      = ng:generate(),
        dispatch = ng:generate(),
        ins      = ng:generate(),
    }

    local handlers = {}

    -- Helper: push a handler entry string
    local function handler(op_name, body)
        local ov = OP[op_name]
        if not ov then return end
        handlers[#handlers + 1] = string.format(
            "[%d]=function(%s,%s,%s,%s,%s,%s) %s end",
            ov,
            N.stack, N.pc, N.proto, N.upvals, N.env, N.ins,
            body
        )
    end

    -- Shorthand accessors (produce strings, not Lua expressions)
    local st  = N.stack
    local pc  = N.pc
    local pt  = N.proto
    local ins = N.ins
    local env = N.env

    local function A()   return ins .. ".a"   end
    local function B()   return ins .. ".b"   end
    local function C()   return ins .. ".c"   end
    local function Bx()  return ins .. ".bx"  end
    local function sBx() return ins .. ".sbx" end

    -- Data movement
    handler("LOADNIL",
        st.."["..A().."]=nil")
    handler("LOADBOOL",
        st.."["..A().."]="..B().."~=0 "..
        "if "..C().."~=0 then "..pc.."[1]="..pc.."[1]+1 end")
    handler("LOADINT",
        st.."["..A().."]="..Bx())
    handler("LOADK",
        st.."["..A().."]="..pt..".constants["..Bx().."+1]")
    handler("MOVE",
        st.."["..A().."]="..st.."["..B().."]")
    handler("GETGLOBAL",
        st.."["..A().."]="..env.."["..pt..".constants["..Bx().."+1]]")
    handler("SETGLOBAL",
        env.."["..pt..".constants["..Bx().."+1]]="..st.."["..A().."]")
    handler("GETTABLE",
        st.."["..A().."]="..st.."["..B().."]["..st.."["..C().."]]")
    handler("SETTABLE",
        st.."["..A().."]["..st.."["..B().."]]="..st.."["..C().."]")
    handler("NEWTABLE",
        st.."["..A().."]={}")
    handler("SETLIST",
        "local _b="..A().." local _n="..B().." local _o=("..C().."-1)*50 "..
        "for _i=1,_n do "..st.."["..st.."[_b]][_o+_i]="..st.."[_b+_i] end")

    -- Arithmetic
    handler("ADD",  st.."["..A().."]="..st.."["..B().."]+"..st.."["..C().."]")
    handler("SUB",  st.."["..A().."]="..st.."["..B().."]- "..st.."["..C().."]")
    handler("MUL",  st.."["..A().."]="..st.."["..B().."]* "..st.."["..C().."]")
    handler("DIV",  st.."["..A().."]="..st.."["..B().."]/ "..st.."["..C().."]")
    handler("MOD",  st.."["..A().."]="..st.."["..B().."]% "..st.."["..C().."]")
    handler("POW",  st.."["..A().."]="..st.."["..B().."]^ "..st.."["..C().."]")
    handler("IDIV", st.."["..A().."]="..st.."["..B().."]// "..st.."["..C().."]")
    handler("UNM",  st.."["..A().."]=-"..st.."["..B().."]")
    handler("NOT",  st.."["..A().."]=not "..st.."["..B().."]")
    handler("LEN",  st.."["..A().."]=# "..st.."["..B().."]")

    -- Concat (binary: A = B .. C)
    handler("CONCAT",
        "local _s=tostring("..st.."["..B().."])"..
        " for _ci="..B().."+1,"..C().." do _s=_s..tostring("..st.."[_ci]) end "..
        st.."["..A().."]= _s")

    -- Comparison (note: ~= inside strings is fine, host never parses it as code)
    handler("EQ",
        (cfg.vm_debug and ("print('[VM] EQ: '..tostring("..st.."["..B().."])..' ('..type("..st.."["..B().."])..')  ==  '..tostring("..st.."["..C().."])..' ('..type("..st.."["..C().."])..')  result='..tostring("..st.."["..B().."]=="..st.."["..C().."])) ") or "") ..
        "local _b,_c="..st.."["..B().."],"..st.."["..C().."] "..
        "local _eq=_b==_c "..
        "if not _eq and type(_b)~=type(_c) then "..
        "_eq=tostring(_b)==tostring(_c) end "..
        "if _eq~=("..A().."~=0) then "..
        pc.."[1]="..pc.."[1]+1 end")
    handler("LT",
        "if ("..st.."["..B().."]<"..st.."["..C().."])~=("..A().."~=0) then "..
        pc.."[1]="..pc.."[1]+1 end")
    handler("LE",
        "if ("..st.."["..B().."]<="..st.."["..C().."])~=("..A().."~=0) then "..
        pc.."[1]="..pc.."[1]+1 end")
    handler("TEST",
        "if (not not "..st.."["..A().."])~=("..C().."~=0) then "..
        pc.."[1]="..pc.."[1]+1 end")
    handler("JMP",
        pc.."[1]="..pc.."[1]+"..sBx())

    -- Calls
    handler("CALL",
        "local _f="..st.."["..A().."] "..
        "local _a={} for _i="..A().."+1,"..A().."+"..B().."-1 do _a[#_a+1]="..st.."[_i] end "..
        "local _r={_f(_unpack(_a))} "..
        "if "..C().."==0 then for _i=1,#_r do "..st.."["..A().."+_i-1]=_r[_i] end "..
        "else for _i=1,"..C().."-1 do "..st.."["..A().."+_i-1]=_r[_i] end end")
    handler("RETURN",
        "local _r={} for _i="..A()..","..A().."+"..B().."-2 do _r[#_r+1]="..st.."[_i] end "..
        "return _unpack(_r)")

    -- Closures — capture enclosing stack as upvalue array so inner functions
    -- can read locals from the parent frame via GETUPVAL/SETUPVAL.
    handler("CLOSURE",
        "local _p="..pt..".protos["..Bx().."+1] "..
        "local _uvs={} "..
        "for _ui=1,#(_p.upvals or {}) do "..
        "  local _ud=_p.upvals[_ui] "..
        "  if _ud.instack then _uvs[_ui]={get=function() return "..st.."[_ud.idx] end,set=function(_v) "..st.."[_ud.idx]=_v end} "..
        "  end "..
        "end "..
        st.."["..A().."]=(function(...) return "..N.execute.."(_p,_uvs,"..env..",...) end)")
    handler("GETUPVAL",
        "if "..N.upvals.." and "..N.upvals.."["..B().."+1] then "..
        st.."["..A().."]="..N.upvals.."["..B().."+1].get() "..
        "else "..st.."["..A().."]=nil end")
    handler("SETUPVAL",
        "if "..N.upvals.." and "..N.upvals.."["..B().."+1] then "..
        N.upvals.."["..B().."+1].set("..st.."["..A().."])"..
        "end")
    handler("VARARG",
        -- upvals table carries a .varargs field populated at frame entry
        "if "..N.upvals.." and type("..N.upvals..")=='table' and "..N.upvals..".varargs then "..
        "  local _va="..N.upvals..".varargs "..
        "  local _b="..B().." "..
        "  if _b<=1 then "..st.."["..A().."]= _va[1] "..
        "  else for _vi=0,_b-2 do "..st.."["..A().."+_vi]=_va[_vi+1] end end "..
        "end")

    -- Bitwise (use bit32 calls — raw operators crash Lua 5.1 / some Roblox executors)
    handler("BAND", st.."["..A().."]=bit32.band("..st.."["..B().."],"..st.."["..C().."])")
    handler("BOR",  st.."["..A().."]=bit32.bor("..st.."["..B().."],"..st.."["..C().."])")
    handler("BXOR", st.."["..A().."]=bit32.bxor("..st.."["..B().."],"..st.."["..C().."])")
    handler("BNOT", st.."["..A().."]=bit32.bnot("..st.."["..B().."])")
    handler("BSHL", st.."["..A().."]=bit32.lshift("..st.."["..B().."],"..st.."["..C().."])")
    handler("BSHR", st.."["..A().."]=bit32.rshift("..st.."["..B().."],"..st.."["..C().."])")

    -- Loops
    handler("FORPREP",
        st.."["..A().."]="..st.."["..A().."]- "..st.."["..A().."+2] "..
        pc.."[1]="..pc.."[1]+"..sBx())
    handler("FORLOOP",
        st.."["..A().."]="..st.."["..A().."]+"..st.."["..A().."+2] "..
        "if ("..st.."["..A().."+2]>0 and "..st.."["..A().."]<="..st.."["..A().."+1]) or "..
        "("..st.."["..A().."+2]<0 and "..st.."["..A().."]>="..st.."["..A().."+1]) then "..
        st.."["..A().."+3]="..st.."["..A().."] "..
        pc.."[1]="..pc.."[1]+"..sBx().." end")

    handler("TFORLOOP",
        (cfg.vm_debug and ("print('[VM] TFORLOOP A="..A().." f='..tostring("..st.."["..A().."])..' s='..tostring("..st.."["..A().."+1])..' c='..tostring("..st.."["..A().."+2])) ") or "") ..
        "local _f="..st.."["..A().."] local _s="..st.."["..A().."+1] local _c="..st.."["..A().."+2] "..
        "local _r={_f(_s,_c)} "..
        (cfg.vm_debug and ("for _di=1,#_r do print('[VM]   TFORLOOP result['.._di..']='..tostring(_r[_di])..' ('..type(_r[_di])..')') end ") or "") ..
        "for _i=1,"..C().." do "..st.."["..A().."+3+_i-1]=_r[_i] end "..
        "if _r[1]~=nil then "..st.."["..A().."+2]=_r[1] else "..pc.."[1]="..pc.."[1]+1 end")

    -- Dummy handlers — look like real complex handlers to confuse reversers
    local dummy_templates = {
        function(s, p, pt2, ins2, ng2)
            local v1, v2, v3 = ng2:generate(), ng2:generate(), ng2:generate()
            return "local "..v1.."="..s.."["..ins2..".a] "..
                   "local "..v2.."="..s.."["..ins2..".b] "..
                   "if "..v1.."~=nil then "..s.."["..ins2..".a]="..v2.." else "..
                   "local "..v3.."="..pt2..".constants["..ins2..".bx+1] "..
                   s.."["..ins2..".a]="..v3.." end"
        end,
        function(s, p, pt2, ins2, ng2)
            local v1, v2 = ng2:generate(), ng2:generate()
            return "local "..v1.."="..ins2..".a+"..ins2..".b "..
                   "local "..v2.."={} for "..ng2:generate().."=0,"..v1.." do "..
                   v2.."[#"..v2.."+1]="..s.."["..ng2:generate().."] or 0 end "..
                   s.."["..ins2..".a]="..v2
        end,
        function(s, p, pt2, ins2, ng2)
            local v1 = ng2:generate()
            return "local "..v1.."=("..s.."["..ins2..".b] or 0)+("..
                   s.."["..ins2..".c] or 0) "..
                   "if "..v1..">255 then "..v1.."=255 end "..
                   s.."["..ins2..".a]="..v1
        end,
        function(s, p, pt2, ins2, ng2)
            local v1, v2 = ng2:generate(), ng2:generate()
            return "local "..v1.."="..pt2..".constants "..
                   "local "..v2.."="..ins2..".bx "..
                   "if "..v1.."["..v2.."+1]~=nil then "..
                   s.."["..ins2..".a]="..v1.."["..v2.."+1] end"
        end,
    }

    for i = 1, (cfg.dummy_opcodes or 20) do
        local ov = OP["DUMMY_" .. i]
        if ov then
            local tmpl = dummy_templates[math.random(1, #dummy_templates)]
            local body = tmpl(N.stack, N.pc, N.proto, N.ins, ng)
            handlers[#handlers + 1] = string.format(
                "[%d]=function(%s,%s,%s,%s,%s,%s) %s end",
                ov,
                N.stack, N.pc, N.proto, N.upvals, N.env, N.ins,
                body
            )
        end
    end


    -- Replace _unpack placeholder in handlers with obfuscated name
    for idx = 1, #handlers do
        handlers[idx] = handlers[idx]:gsub("_unpack", n_unpack)
    end

    -- Split dispatch into 2-3 sub-tables then merge (confuses pattern matching)
    local split_a, split_b = {}, {}
    for idx, h in ipairs(handlers) do
        if idx % 2 == 0 then
            split_b[#split_b + 1] = h
        else
            split_a[#split_a + 1] = h
        end
    end
local fake_hash_body = string.format(
    "local %s=0 for %s=1,#%s.code do %s=%s+%s.code[%s].op end return %s",
    fh_accum, fh_iter, n_proto_guard,
    fh_accum, fh_accum, n_proto_guard, fh_iter, fh_accum
)
    local parts = {}

    parts[#parts + 1] = "local " .. n_unpack  .. "=unpack or table.unpack\n"
    parts[#parts + 1] = "local " .. n_getfenv .. "=getfenv or function() return _G end\n"
    parts[#parts + 1] = "local " .. n_select  .. "=select\n"
    parts[#parts + 1] = "local " .. n_type    .. "=type\n"
    parts[#parts + 1] = "local " .. n_pcall   .. "=pcall\n"
    -- Fake guard function
parts[#parts + 1] = "local " .. n_guard .. "=function(" .. n_proto_guard .. ") " .. fake_hash_body .. " end\n"
    -- Forward-declare execute so CLOSURE handlers can reference it
    parts[#parts + 1] = "local " .. N.execute .. "\n"
    -- Split dispatch
    parts[#parts + 1] = "local " .. n_da .. "={" .. table.concat(split_a, ",") .. "}\n"
    parts[#parts + 1] = "local " .. n_db .. "={" .. table.concat(split_b, ",") .. "}\n"
    parts[#parts + 1] = "local " .. N.dispatch .. "={}\n"
    parts[#parts + 1] = "for " .. lv1 .. "," .. lv2 .. " in pairs(" .. n_da .. ") do " .. N.dispatch .. "[" .. lv1 .. "]=" .. lv2 .. " end\n"
    parts[#parts + 1] = "for " .. lv3 .. "," .. lv4 .. " in pairs(" .. n_db .. ") do " .. N.dispatch .. "[" .. lv3 .. "]=" .. lv4 .. " end\n"
    -- Main VM loop
    parts[#parts + 1] = N.execute .. "=function(" .. N.proto .. "," .. N.upvals .. "," .. N.env .. ",...)\n"
    parts[#parts + 1] = "  local " .. N.pc    .. "={1}\n"
    parts[#parts + 1] = "  local " .. N.stack .. "={}\n"
    parts[#parts + 1] = "  do local _a={...} for _i=1,#_a do " .. N.stack .. "[_i-1]=_a[_i] end end\n"
    parts[#parts + 1] = "  " .. N.env .. "=" .. N.env .. " or " .. n_getfenv .. "()\n"
    -- Fake integrity call (always runs, does nothing harmful)
    parts[#parts + 1] = "  local " .. n_tick .. "=" .. n_guard .. "(" .. N.proto .. ")\n"
    parts[#parts + 1] = "  while " .. N.pc .. "[1]<=#" .. N.proto .. ".code do\n"
    parts[#parts + 1] = "    local " .. N.ins .. "=" .. N.proto .. ".code[" .. N.pc .. "[1]]\n"
    parts[#parts + 1] = "    if not " .. N.ins .. " then break end\n"
    parts[#parts + 1] = "    " .. N.pc .. "[1]=" .. N.pc .. "[1]+1\n"
    parts[#parts + 1] = "    local _h=" .. N.dispatch .. "[" .. N.ins .. ".op]\n"
    if cfg.vm_debug then
        -- Build reverse opcode name table
        local op_name_entries = {}
        for name, val in pairs(OP) do
            if not name:match("^DUMMY_") then
                op_name_entries[#op_name_entries + 1] = string.format("[%d]=%q", val, name)
            end
        end
        local n_opnames = ng:generate()
        parts[#parts + 1] = "    local " .. n_opnames .. "={" .. table.concat(op_name_entries, ",") .. "}\n"
        -- Print opcode info
        parts[#parts + 1] = "    print('[VM] pc='..((" .. N.pc .. "[1])-1)"
            .. "..' op='..tostring(" .. n_opnames .. "[" .. N.ins .. ".op] or " .. N.ins .. ".op)"
            .. "..' a='..tostring(" .. N.ins .. ".a)"
            .. "..' b='..tostring(" .. N.ins .. ".b)"
            .. "..' c='..tostring(" .. N.ins .. ".c)"
            .. "..' bx='..tostring(" .. N.ins .. ".bx)"
            .. "..' sbx='..tostring(" .. N.ins .. ".sbx)"
            .. ")\n"
        -- Extra detail for CALL: show what's in the function register
        local call_op = tostring(OP.CALL)
        parts[#parts + 1] = "    if " .. N.ins .. ".op==" .. call_op .. " then\n"
        parts[#parts + 1] = "      local _da=" .. N.ins .. ".a\n"
        parts[#parts + 1] = "      print('[VM]   CALL func: stack['.._da..']='..tostring(" .. N.stack .. "[_da])..' ('..type(" .. N.stack .. "[_da])..')')\n"
        parts[#parts + 1] = "      for _di=_da+1,_da+" .. N.ins .. ".b-1 do print('[VM]   arg stack['.._di..']='..tostring(" .. N.stack .. "[_di])..' ('..type(" .. N.stack .. "[_di])..')') end\n"
        parts[#parts + 1] = "    end\n"
    end
    parts[#parts + 1] = "    if _h then _h(" .. N.stack .. "," .. N.pc .. "," .. N.proto .. "," .. N.upvals .. "," .. N.env .. "," .. N.ins .. ") end\n"
    parts[#parts + 1] = "  end\n"
    parts[#parts + 1] = "end\n"
    parts[#parts + 1] = N.execute .. "(" .. proto_str .. ",{...}," .. n_getfenv .. "())\n"
    return table.concat(parts)
end

-- ── Rolling XOR (host-side, uses bit32 shim) ─────────────────────
function VM.rolling_xor_encrypt(data, key)
    local out  = {}
    local prev = 0
    for i = 1, #data do
        local k = key:byte(((i - 1) % #key) + 1)
        local b = _bxor(_bxor(data:byte(i), k), prev)
        out[i]  = string.char(b)
        prev    = b
    end
    return table.concat(out)
end

-- Generates the Luau loader stub (runs inside executor, Luau syntax OK)
-- Uses chunked string.char to build the encrypted data string instead
-- of a huge table literal that would blow the register limit.
function VM.rolling_xor_loader(encrypted, key)
    local k_bytes = {}
    for i = 1, #key do k_bytes[i] = tostring(key:byte(i)) end

    -- Build encrypted data as a string using chunked string.char
    local parts = {}
    parts[#parts + 1] = "local _d=" .. chunked_string_char(encrypted)
    parts[#parts + 1] = "local _k={" .. table.concat(k_bytes, ",") .. "}"
    parts[#parts + 1] = "local _t={} local _p=0"
    parts[#parts + 1] = "for _i=1,#_d do"
    parts[#parts + 1] = "  local _b=string.byte(_d,_i)"
    parts[#parts + 1] = "  local _x=bit32.bxor(bit32.bxor(_b,_k[((_i-1)%" .. tostring(#key) .. ")+1]),_p)"
    parts[#parts + 1] = "  _t[_i]=string.char(_x) _p=_x"
    parts[#parts + 1] = "end"
    parts[#parts + 1] = "loadstring(table.concat(_t))()"
    return table.concat(parts, "\n") .. "\n"
end

-- ── Public API ────────────────────────────────────────────────────
-- Lazy-load parser and lexer (handles both require and loadfile)
local _Lexer, _Parser
local function get_lexer()
    if _Lexer then return _Lexer end
    local ok, m = pcall(require, "lexer")
    if ok then _Lexer = m; return m end
    local chunk = loadfile("src/lexer.lua") or loadfile("lexer.lua")
    if chunk then _Lexer = chunk(); return _Lexer end
    error("[VM] Cannot load lexer.lua")
end
local function get_parser()
    if _Parser then return _Parser end
    local ok, m = pcall(require, "parser")
    if ok then _Parser = m; return m end
    local chunk = loadfile("src/parser.lua") or loadfile("parser.lua")
    if chunk then _Parser = chunk(); return _Parser end
    error("[VM] Cannot load parser.lua")
end

function VM:compile(source)
    local Lexer  = get_lexer()
    local Parser = get_parser()

    local lexer  = Lexer.new(source)
    local tokens = lexer:tokenize()
    local ast    = Parser.parse(tokens, Lexer.TOKEN, Lexer)

    local compiler = Compiler.new(self)
    compiler:compile_node(ast)
    local proto = compiler:finalize()

    -- Debug: dump top-level constant table so bx indices can be verified
    if self.cfg and self.cfg.vm_debug then
        io.stderr:write("[Compiler] Top-level constants (0-based bx index):\n")
        for i, v in ipairs(proto.constants) do
            io.stderr:write(string.format("  bx=%-4d  %s\n", i - 1, tostring(v)))
        end
    end

    return proto
end

function VM:bundle(proto, cfg, namegen)
    local proto_str = serialize_proto(proto)
    local vm_source = self:build_interpreter_source(proto_str, cfg, namegen)

    if cfg.bytecode_encryption then
        local key = {}
        for i = 1, 32 do key[i] = string.char(math.random(32, 126)) end
        key = table.concat(key)
        local encrypted = VM.rolling_xor_encrypt(vm_source, key)
        vm_source = VM.rolling_xor_loader(encrypted, key)
    end

    -- ── Outer wrapper: hex blob + XOR decode + intimidation layer ───
    -- Instead of string.char(n,n,n...) we encode as a hex string
    -- decoded through a keyed XOR with obfuscated names.

    local ng = namegen or error("VM:bundle requires a namegen object")


    -- Generate a random XOR key
    local key_len = math.random(24, 48)
    local xor_key = {}
    for i = 1, key_len do xor_key[i] = math.random(1, 254) end

    -- XOR-encode the VM source
    local encoded = {}
    for i = 1, #vm_source do
        local b = vm_source:byte(i)
        local k = xor_key[((i - 1) % key_len) + 1]
        encoded[i] = string.format("%02x", _bxor(b, k))
    end
    local hex_blob = table.concat(encoded)

    -- Key as hex
    local key_hex = {}
    for i = 1, key_len do key_hex[i] = string.format("%02x", xor_key[i]) end
    local key_str = table.concat(key_hex)

    -- Obfuscated names (only those used in the surviving code path)
    local n_blob     = ng:generate()
    local n_key      = ng:generate()
    local n_out      = ng:generate()
    local n_i        = ng:generate()
    local n_b        = ng:generate()
    local n_sub      = ng:generate()
    local n_char     = ng:generate()
    local n_tonumber = ng:generate()
    local n_exec     = ng:generate()
    local n_guard1   = ng:generate()
    local n_ver      = ng:generate()

    -- Split hex blob into chunks stored in a single table (avoids blowing 200 local limit)
    local blob_chunk_size = math.random(800, 1200)
    local n_blob_tbl = ng:generate()
    local blob_lines = {}
    local chunk_strs = {}
    local pos = 1
    while pos <= #hex_blob do
        local chunk = hex_blob:sub(pos, pos + blob_chunk_size - 1)
        chunk_strs[#chunk_strs + 1] = '"' .. chunk .. '"'
        pos = pos + blob_chunk_size
    end
    blob_lines[#blob_lines + 1] = "local " .. n_blob_tbl .. "={" .. table.concat(chunk_strs, ",") .. "}"
    blob_lines[#blob_lines + 1] = "local " .. n_blob .. "=table.concat(" .. n_blob_tbl .. ")"

    -- Build the wrapper — allocate all loop/decode names up front
    local n_kl  = ng:generate()
    local n_idx = ng:generate()
    local n_ki  = ng:generate()
    local n_kv  = ng:generate()
    local n_xor = ng:generate()

    local lines = {}

    local build_id = os.time()

    lines[#lines + 1] = '--[[ Dawn Virtual Engine | Build ' .. build_id .. ' | github.com/dawn-obf ]]'
    lines[#lines + 1] = '--[[ This script is protected. Decompilation/modification is prohibited. ]]'
    lines[#lines + 1] = ''

    -- ── Entry loader: VM-style preamble that looks like real interpreter internals ──
    if cfg.entry_loader then
        lines[#lines + 1] = "do"
        -- Generate a bunch of realistic-looking names
        local n_rt      = ng:generate()
        local n_sig     = ng:generate()
        local n_iv      = ng:generate()
        local n_harden  = ng:generate()
        local n_regs    = ng:generate()
        local n_tape    = ng:generate()
        local n_alloc   = ng:generate()
        local n_digest  = ng:generate()
        local n_digest2 = ng:generate()
        local n_frame   = ng:generate()
        local n_ctx     = ng:generate()
        local n_vmstate = ng:generate()
        local n_opmap   = ng:generate()
        local n_intchk  = ng:generate()
        local n_segA    = ng:generate()
        local n_segB    = ng:generate()
        local n_pipeline = ng:generate()
        local n_decoder  = ng:generate()
        local n_verify   = ng:generate()
        local n_p0,n_p1,n_p2,n_p3 = ng:generate(),ng:generate(),ng:generate(),ng:generate()

        -- Random hex strings for fake signatures/IVs/digests
        local function rand_hex(len)
            local h = {}
            for ri = 1, len do h[ri] = string.format("%02X", math.random(0,255)) end
            return table.concat(h)
        end
        local function rand_hex_dashed()
            return rand_hex(2).."-"..rand_hex(2).."-"..rand_hex(2).."-"..rand_hex(2)
        end

        -- Random opcode tape values
        local tape_vals = {}
        for ti = 1, math.random(16, 32) do
            tape_vals[ti] = tostring(math.random(0, 255))
        end

        -- Random register count
        local reg_count = math.random(6, 12)
        local reg_inits = {}
        for ri = 1, reg_count do reg_inits[ri] = "0" end

        -- Random allocation table entries
        local alloc_entries = {}
        local seg_labels = {"A","B","C","D","E","F"}
        for ai = 1, math.random(4, 8) do
            local label = seg_labels[math.random(1,#seg_labels)] .. tostring(math.random(0,9))
            alloc_entries[ai] = '["' .. label .. '"]=' .. (math.random() > 0.5 and "true" or "false")
        end

        -- Runtime metadata block
        lines[#lines + 1] = "local " .. n_rt .. "=setmetatable({"
        lines[#lines + 1] = '  ' .. ng:generate() .. '=0x' .. string.format("%04X", math.random(0, 65535)) .. ','
        lines[#lines + 1] = '  ' .. n_iv .. '="' .. rand_hex_dashed() .. '",'
        lines[#lines + 1] = '  ' .. n_sig .. '="DVE-' .. rand_hex(3) .. '",'
        lines[#lines + 1] = '  ' .. n_harden .. '=true,'
        lines[#lines + 1] = "},{__index=function() return nil end})"
        lines[#lines + 1] = ''

        -- Register bank
        lines[#lines + 1] = "local " .. n_regs .. "={" .. table.concat(reg_inits, ",") .. "}"
        lines[#lines + 1] = ''

        -- Opcode tape
        lines[#lines + 1] = "local " .. n_tape .. "={"
        -- Split tape into rows of 8
        for ti = 1, #tape_vals, 8 do
            local row = {}
            for ri = ti, math.min(ti + 7, #tape_vals) do
                row[#row + 1] = tape_vals[ri]
            end
            lines[#lines + 1] = "  " .. table.concat(row, ",") .. ","
        end
        lines[#lines + 1] = "}"
        lines[#lines + 1] = ''

        -- Allocation table
        lines[#lines + 1] = "local " .. n_alloc .. "={"
        lines[#lines + 1] = "  " .. table.concat(alloc_entries, ",")
        lines[#lines + 1] = "}"
        lines[#lines + 1] = ''

        -- Key digests
        lines[#lines + 1] = "local " .. n_digest  .. '="' .. rand_hex_dashed() .. '"'
        lines[#lines + 1] = "local " .. n_digest2 .. '="' .. rand_hex_dashed() .. '"'
        lines[#lines + 1] = ''

        -- VM state + opcode map (all dead but looks real)
        lines[#lines + 1] = "local " .. n_vmstate .. "={" .. ng:generate() .. "=0," .. ng:generate() .. "=false," .. ng:generate() .. '="idle"}'
        lines[#lines + 1] = "local " .. n_opmap .. "={}"
        lines[#lines + 1] = "for " .. n_p0 .. "=0," .. tostring(math.random(40, 80)) .. " do " .. n_opmap .. "[" .. n_p0 .. "]=bit32.bxor(" .. n_p0 .. "," .. tostring(math.random(1, 255)) .. ") end"
        lines[#lines + 1] = ''

        -- Integrity check function (runs but does nothing meaningful)
        lines[#lines + 1] = "local " .. n_intchk .. "=function(" .. n_p1 .. ")"
        lines[#lines + 1] = "  local " .. n_p2 .. "=0"
        lines[#lines + 1] = "  for " .. n_p3 .. "=1,#" .. n_tape .. " do"
        lines[#lines + 1] = "    " .. n_p2 .. "=bit32.bxor(" .. n_p2 .. "," .. n_tape .. "[" .. n_p3 .. "])"
        lines[#lines + 1] = "  end"
        lines[#lines + 1] = "  return bit32.band(" .. n_p2 .. ",0xFFFF)"
        lines[#lines + 1] = "end"
        lines[#lines + 1] = ''

        -- Execution frame (looks like interpreter bootstrap)
        lines[#lines + 1] = "local " .. n_frame .. "=function(" .. n_segA .. "," .. n_segB .. ")"
        lines[#lines + 1] = "  local " .. n_pipeline .. "=" .. n_opmap .. "[bit32.band(" .. n_segA .. ",0x3F)] or 0"
        lines[#lines + 1] = "  local " .. n_decoder .. "=bit32.bxor(" .. n_segB .. "," .. n_pipeline .. ")"
        lines[#lines + 1] = "  " .. n_regs .. "[1]=bit32.band(" .. n_decoder .. ",0xFF)"
        lines[#lines + 1] = "  return " .. n_decoder
        lines[#lines + 1] = "end"
        lines[#lines + 1] = ''

        -- Run the integrity check (actually executes, result unused)
        lines[#lines + 1] = "local " .. n_verify .. "=" .. n_intchk .. "(" .. n_rt .. ")"
        lines[#lines + 1] = n_vmstate .. "." .. ng:generate() .. "=" .. n_verify
        lines[#lines + 1] = ''

        -- Context table that ties it all together visually
        lines[#lines + 1] = "local " .. n_ctx .. "={"
        lines[#lines + 1] = "  " .. ng:generate() .. "=" .. n_rt .. ","
        lines[#lines + 1] = "  " .. ng:generate() .. "=" .. n_regs .. ","
        lines[#lines + 1] = "  " .. ng:generate() .. "=" .. n_alloc .. ","
        lines[#lines + 1] = "  " .. ng:generate() .. "=" .. n_frame .. ","
        lines[#lines + 1] = "  " .. ng:generate() .. "=" .. n_verify .. ","
        lines[#lines + 1] = "}"
        lines[#lines + 1] = ''
        lines[#lines + 1] = "end"
    end

    -- ── Real decode logic (wrapped in do...end to scope locals) ────
    lines[#lines + 1] = "do"
    lines[#lines + 1] = "local " .. n_ver    .. '="Dawn-4.' .. math.random(1,9) .. '.' .. math.random(0,99) .. '"'
    lines[#lines + 1] = "local " .. n_guard1 .. "=tostring"

    -- Alias builtins with obfuscated names
    lines[#lines + 1] = "local " .. n_sub      .. "=string.sub"
    lines[#lines + 1] = "local " .. n_char     .. "=string.char"
    lines[#lines + 1] = "local " .. n_tonumber .. "=tonumber"

    -- Key
    lines[#lines + 1] = 'local ' .. n_key .. '="' .. key_str .. '"'

    -- Blob chunks
    for _, l in ipairs(blob_lines) do
        lines[#lines + 1] = l
    end
    -- Decode
    lines[#lines + 1] = "local " .. n_out .. "={}"
    lines[#lines + 1] = "local " .. n_kl .. "=" .. tostring(key_len)
    lines[#lines + 1] = "for " .. n_i .. "=1,#" .. n_blob .. ",2 do"
    lines[#lines + 1] = "  local " .. n_b .. "=" .. n_tonumber .. "(" .. n_sub .. "(" .. n_blob .. "," .. n_i .. "," .. n_i .. "+1),16)"
    lines[#lines + 1] = "  local " .. n_idx .. "=(" .. n_i .. "-1)/2%" .. tostring(key_len)
    lines[#lines + 1] = "  local " .. n_kv .. "=" .. n_tonumber .. "(" .. n_sub .. "(" .. n_key .. "," .. n_idx .. "*2+1," .. n_idx .. "*2+2),16)"
    lines[#lines + 1] = "  local " .. n_xor .. "=bit32.bxor(" .. n_b .. "," .. n_kv .. ")"
    lines[#lines + 1] = "  " .. n_out .. "[#" .. n_out .. "+1]=" .. n_char .. "(" .. n_xor .. ")"
    lines[#lines + 1] = "end"
    -- Execute
    lines[#lines + 1] = "local " .. n_exec .. "=table.concat(" .. n_out .. ")"
    lines[#lines + 1] = "assert(loadstring(" .. n_exec .. "))()"
    lines[#lines + 1] = "end"

    return table.concat(lines, "\n")
end

VM.Compiler = Compiler
return VM
