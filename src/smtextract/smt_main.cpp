#include "smt_extract.h"
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <stdio.h>
#include <string>
#include <sys/stat.h>
#include <unordered_map>
#include <vector>

const std::string bsq_cmds_dir = "../../../../bin/src/cmd";

// MOCK_RUNNER,
// TEST_RUNNER,
typedef enum _ExtractorMode
{
    MOCK_RUNNER,
    TEST_RUNNER,
} ExtractorMode;

// Mock Name, target_type_info
//
// std::pmr::unordered_map<std::string, std::string> mock_signatures;
// std::vector<std::string> bsq_files;
// std::string smt_file;
// std::string type_info;
// ExtractorMode mode;
typedef struct _ExtractorMetadata
{
    std::vector<std::string> bsq_files;
    std::pmr::unordered_map<std::string, json> mock_signatures;
    std::string smt_file;
    json type_info;
    ExtractorMode mode;
} ExtractorMetadata;

void printUsage(const char* msg)
{
    const char* usage = "USAGE: smtextract <BSQFILES> --functions <MOCKNAMES>\n"
                        "\t-t|--test      - Use extractor for tests. Returns args of mocks.\n"
                        "\t-m|--mock      - Use extractor at runtime. Returns result of mock.";

    printf("%s\n", usage);
    printf("%s\n", msg);
    exit(1);
}

char* readFile(const char* filename)
{
    FILE* f = fopen(filename, "r");
    if (!f)
    {
        perror("fopen");
    }
    fseek(f, 0, SEEK_END);
    long length = ftell(f);
    rewind(f);
    char* bfr = (char*)malloc(sizeof(char) * length);

    fread(bfr, sizeof(char), length, f);

    fclose(f);
    return bfr;
}

std::optional<z3::expr> findConstantInModel(z3::model m, std::string id)
{
    uint n_consts = m.num_consts();
    for (uint i = 0; i < n_consts; ++i)
    {
        z3::func_decl fn_const = m.get_const_decl(i);
        std::string fn_id = fn_const.name().str();

        if (fn_id == id)
        {
            return fn_const();
        }
    }

    return std::nullopt;
}

std::pmr::unordered_map<std::string, std::string> getValidators(z3::model m)
{
    std::pmr::unordered_map<std::string, std::string> validator_map;

    for (uint i = 0; i < m.num_funcs(); ++i)
    {
        z3::func_decl fn = m.get_func_decl(i);
        std::string fn_str = fn.name().str();

        // Skip anything that doesn't have "@Validate"
        if (fn_str.find("@Validate") == std::string::npos)
        {
            continue;
        }

        // Split at the first '-'
        size_t sep = fn_str.find('-');
        if (sep == std::string::npos)
        {
            continue;
        }

        std::string validator_type = fn_str.substr(0, sep);
        std::string validator_sort = fn_str.substr(sep + 1);
        if (validator_sort.empty() || validator_type.empty())
        {
            continue;
        }

        bool is_root_validator = (validator_type.find("Root") != std::string::npos);

        auto it = validator_map.find(validator_sort);

        if (it == validator_map.end())
        {
            // First time we see this sort — store it
            validator_map.emplace(validator_sort, fn_str);
        }
        else
        {
            // Already have one — replace only if new one is Root and old isn't
            bool existing_is_root = (it->second.find("Root") != std::string::npos);
            if (is_root_validator && !existing_is_root)
            {
                it->second = fn_str;
            }
            // else: ignore (keep the existing Root or existing non-root)
        }
    }

    return validator_map;
}

std::string validateReturn(std::pmr::unordered_map<std::string, json> mock_signatures,
                           std::pmr::unordered_map<bsqon::TypeKey, std::string> validator_map)
{
    std::string validating_mocks;
    for (auto& mock : mock_signatures)
    {
        bsqon::TypeKey tkey = mock.second["return"];
        std::string tkey_smt = tKeyToSmtName(tkey, SMT_TYPE);

        std::string mock_validator = validator_map.at(tkey_smt);

        validating_mocks += "(assert (" + mock_validator + " " + "@retMock-" + tkey_smt + "))";
    }

    return validating_mocks;
}

std::string validateParameters(std::pmr::unordered_map<std::string, json> mock_signatures,
                               std::pmr::unordered_map<bsqon::TypeKey, std::string> validator_map)
{
    std::string validating_mocks;

    for (auto& mock : mock_signatures)
    {
        for (auto arg : mock.second["args"])
        {
			std::string id = arg["name"];
			bsqon::TypeKey tkey = arg["type"];
            std::string tkey_smt = tKeyToSmtName(tkey, SMT_TYPE);

            std::string mock_validator = validator_map.at(tkey_smt);

            validating_mocks += "(assert (" + mock_validator + " " + "@retMock-" + tkey_smt + "))";
        }
    }
    return validating_mocks;
}

// TODO: Pass variable names that need to be looked for here.
std::string patchSMTFormula(std::string smt_file, std::pmr::unordered_map<std::string, json> mock_signatures,
                            ExtractorMode mode)
{
    // HACK: Fix to prevent z3 to optimize the functions that use define-fun.
    std::string helper_fn = ";;;;;;;;;;;;;;;\n (declare-fun MockTest (Int) Int) "
                            "(assert (> (MockTest 5) 2))";
    z3::context c;
    z3::solver sol(c);
    std::string formula = smt_file + helper_fn;
    sol.from_string(formula.c_str());
    z3::check_result cr = sol.check();
    if (cr != z3::sat)
    {
        std::cout << "Got " << cr << " from .smt2 file while patching.";
        exit(1);
    }

    std::string validate_sorts = " ";

    z3::model m = sol.get_model();

    std::pmr::unordered_map<bsqon::TypeKey, std::string> validators = getValidators(m);
    switch (mode)
    {
    case (MOCK_RUNNER):
        validate_sorts = validateReturn(mock_signatures, validators);
        break;
    case (TEST_RUNNER):
        validate_sorts = validateParameters(mock_signatures, validators);
        break;
    }

    std::string smt_formula = smt_file + helper_fn + validate_sorts;

    return smt_formula;
}

std::vector<std::string> processFunctionArg(int start, int end, char** argv)
{
    std::vector<std::string> mocks;
    for (int i = start; i < end; ++i)
    {
        std::string mock_name(argv[i]);
        if (mock_name.find("--") == std::string::npos)
        {
            if (mock_name.find(".bsq") == std::string::npos)
            {
                mocks.push_back(mock_name);
            }
        }
        else
        {
            break;
        }
    }

    return mocks;
}

std::string runBosqueCompiler(std::string cmd)
{
    FILE* output = popen(cmd.c_str(), "r");
    if (!output)
    {
        perror("popen failed");
    }

    std::string result;
    char buffer[1024];

    while (fgets(buffer, sizeof(buffer), output))
    {
        result += buffer; // Accumulate safely
    }

    int status = pclose(output);
    if (status != 0)
    {
        std::cout << "Bosque compiler exited: " << status << "\n";
        exit(status);
    }

    return result;
}

void processBsqFiles(ExtractorMetadata* meta)
{
    std::string gen_bsq_script = bsq_cmds_dir + "/bosque.js";
    std::string gen_smt_script = bsq_cmds_dir + "/analyze.js";
    std::string tmp_dir = "/tmp/smtextract";
    mkdir(tmp_dir.c_str(), 0777);
    std::string jsout_dir = tmp_dir + "/jsout";
    std::string smtout_dir = tmp_dir + "/smtout";
    std::string files = "";

    for (std::string file : meta->bsq_files)
    {
        files = files + " " + file;
    }

    std::string step = "node " + gen_bsq_script + files + " --function ";

    for (auto& sig : meta->mock_signatures)
    {
        std::string mock_name = sig.first;
        std::string run_cmd = step + mock_name + " --output " + jsout_dir;

        std::string compile_ouput = runBosqueCompiler(run_cmd);

        std::string target_type_dir = jsout_dir + "/targettype.json";
        std::string sig_info = readFile(target_type_dir.c_str());

        meta->mock_signatures[sig.first] = json::parse(sig_info);
    }

    std::string type_info_dir = jsout_dir + "/typeinfo.json";
    meta->type_info = json::parse(readFile(type_info_dir.c_str()));

    std::string smt_cmd = "node " + gen_smt_script + files + " --output " + smtout_dir;
    std::string smt_ouput = runBosqueCompiler(smt_cmd);
    std::string smtfile_dir = smtout_dir + "/formula.smt2";

    meta->smt_file = patchSMTFormula(readFile(smtfile_dir.c_str()), meta->mock_signatures, meta->mode);
}

ExtractorMetadata* processArgs(int argc, char** argv)
{
    ExtractorMetadata* meta = new ExtractorMetadata();

    for (int i = 1; i < argc; ++i)
    {
        std::string current_cmd(argv[i]);
        if (current_cmd.find(".bsq") != std::string::npos)
        {
            meta->bsq_files.push_back(current_cmd);
        }
        else if (current_cmd == "--functions" || current_cmd == "-f")
        {
            std::vector<std::string> mock_names = processFunctionArg(i + 1, argc, argv);
            assert(mock_names.size() > 0);
            for (size_t j = 0; j < mock_names.size(); ++j)
            {
                std::string fn = mock_names[j];
                meta->mock_signatures[fn];
            }
        }
        else if (current_cmd == "--mock" || current_cmd == "-m")
        {
            meta->mode = MOCK_RUNNER;
        }
        else if (current_cmd == "--test" || current_cmd == "-t")
        {
            meta->mode = TEST_RUNNER;
        }
    }

    if (meta->mode != MOCK_RUNNER && meta->mode != TEST_RUNNER)
    {
        printUsage("MISSING MODE.");
        exit(1);
    }

    processBsqFiles(meta);
    assert(meta->smt_file.empty() == false && meta->type_info.empty() == false);

    return meta;
}

void extractValue(bsqon::AssemblyInfo* asm_info, ExtractSig ret, z3::solver& sol)
{
    ValueExtractor extractor(asm_info, sol);
    bsqon::Value* c_val = extractor.extractValue(ret.type, ret.ex);

    printf("Type: %s\n", (const char*)ret.type->tkey.c_str());
    printf("Value: %s\n", (const char*)c_val->toString().c_str());
}

void runMockToResult(bsqon::AssemblyInfo* asm_info, json mock_json, z3::solver& sol)
{
    std::string ret_id = "";
    bsqon::TypeKey tkey = mock_json["return"];
    bsqon::Type* ret_t = asm_info->lookupTypeKey(tkey);
    ret_id = "@retMock-" + tKeyToSmtName(tkey, SMT_TYPE);

    z3::check_result cr = sol.check();
    if (cr != z3::sat)
    {
        std::cout << "Got " << cr << " from .smt2 file";
        exit(1);
    }

    z3::model m = sol.get_model();

    auto const_ex = findConstantInModel(m, ret_id);
    if (!const_ex.has_value())
    {
        std::cout << "Unable to find " << ret_id << " in z3 model.\n";
        exit(1);
    }

    ExtractSig sig = {
        .type = ret_t,
        .ex = const_ex.value(),
    };

    extractValue(asm_info, sig, sol);
}

void runMockToArgs(bsqon::AssemblyInfo* asm_info, json mock_json, z3::solver& sol)
{
    for (auto arg : mock_json["args"])
    {
        std::string id = arg["name"];
        bsqon::TypeKey tkey = arg["type"];
        bsqon::Type* arg_t = asm_info->lookupTypeKey(tkey);

        z3::model m = sol.get_model();
        z3::expr arg_ex(sol.ctx());

        ExtractSig sig = {
            .type = arg_t,
            .ex = arg_ex,
        };

        std::string arg_id = "@arg-" + id;
        auto const_ex = findConstantInModel(m, arg_id);
        if (!const_ex.has_value())
        {
            std::cout << "Unable to find " << arg_id << " in z3 model.\n";
            exit(1);
        }

        extractValue(asm_info, sig, sol);
    }
}

int main(int argc, char** argv)
{
    if (argc < 1)
        printUsage("");

    ExtractorMetadata* arg_meta = processArgs(argc, argv);

    // Load SMT FILE
    z3::context c;
    z3::solver sol(c);
    sol.from_string(arg_meta->smt_file.c_str());

    z3::check_result chk_smt = sol.check();
    if (chk_smt == z3::unsat)
    {
        printUsage("Unsat smt file\n");
    }
    else if (chk_smt == z3::unknown)
    {
        printUsage("Unknown smt file\n");
    }

    // Load TYPEINFO FILE
    bsqon::AssemblyInfo asm_info;

    bsqon::AssemblyInfo::parse(arg_meta->type_info, asm_info);
    bsqon::loadAssembly(arg_meta->type_info, asm_info);

    // Load FN INFO FILE
    for (auto& mock_sig : arg_meta->mock_signatures)
    {

        switch (arg_meta->mode)
        {
        case MOCK_RUNNER:
            runMockToResult(&asm_info, mock_sig.second, sol);
            break;
        case TEST_RUNNER:
            runMockToArgs(&asm_info, mock_sig.second, sol);
            break;
        };
    }

    Z3_finalize_memory();
    return 0;
}
