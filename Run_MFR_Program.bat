@echo off
title Harold Birkett's Manufacturing Report Program (Version 2.1)
cd /d "%~dp0"
echo ============================================================================
echo   HAROLD BIRKETT'S MANUFACTURING REPORT PROGRAM (VERSION 2.1)
echo   Wang 2200 BASIC-2 / Niakwa Legacy Remake - Web Application
echo ============================================================================
echo.
python "%~dp0app.py"
if errorlevel 1 (
    echo.
    echo [ERROR] Python encountered an error or is not in PATH.
    pause
)
