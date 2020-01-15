
import pytest
import p4z3.util as util


def pytest_report_teststatus(report):
    if report.when == "call" and report.custom_err == util.EXIT_VIOLATION:
        category = report.outcome
        short = 'v'
        verbose = ('VIOLATION', {"purple": True})
        return category, short, verbose


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item):
    outcome = yield
    report = outcome.get_result()
    report.custom_err = getattr(item, 'custom_err', 0)


# def pytest_collection_modifyitems(config, items):
#     keywordexpr = config.option.keyword
#     markexpr = config.option.markexpr
#     if keywordexpr or markexpr:
#         return  # let pytest handle this

#     skip_p4xfail = pytest.mark.skip(reason='xfail not selected')
#     for item in items:
#         if "p4xfail" in item.keywords:
#             item.add_marker(skip_p4xfail)


def pytest_collection_modifyitems(items, config):
    # add `always_run` marker to all unmarked items
    # for item in items:
    #     if not any(item.iter_markers()):
    #         item.add_marker("always_run")
    # Ensure the `always_run` marker is always selected for
    markexpr = config.getoption("markexpr", "False")
    keyword = config.getoption("keyword", "False")
    if keyword:
        config.option.keyword = keyword
    elif markexpr:
        config.option.markexpr = markexpr
    else:
        config.option.markexpr = f"always_run"
