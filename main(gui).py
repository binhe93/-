#!/usr/bin/env python3
"""
俄语剪贴板朗读器 - 重音标注+形态学分析版 (GUI)
功能：监控剪贴板，当复制俄语文本时，生成并朗读语音，同时标注重音位置和显示中文翻译。
特点：
  1. 使用tsnorm库自动为俄语文本标注重音
  2. 使用deep_translator库进行俄语到中文的翻译
  3. 独立增强俄语语音文件的音量
  4. 提供完整的错误处理和回退机制
  5. 图形化界面，可配置参数
  6. 可自定义朗读时间间隔
  7. 捐赠和支持页面
  8. 形态学分析功能（新增）
  9. 单词历史记录和导出功能（新增）
注意：每次复制都会朗读，即使是相同的内容。
"""

import sys
import os
import time
import re
import subprocess
import warnings
import json
import pickle
from datetime import datetime
from collections import OrderedDict

# PySide6 GUI库
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QSpinBox, QDoubleSpinBox, QCheckBox, QPushButton,
    QTextEdit, QGroupBox, QTabWidget, QFrame, QMessageBox, QGridLayout,
    QScrollArea, QSizePolicy, QInputDialog, QFileDialog  # 新增QFileDialog
)
from PySide6.QtCore import Qt, QThread, Signal, QTimer
from PySide6.QtGui import QFont, QTextCursor, QIcon, QPixmap

# 原有功能库
import pyperclip
from gtts import gTTS
from pydub import AudioSegment

# 形态学分析库
try:
    import pymorphy3
    MORPH_AVAILABLE = True
except ImportError:
    MORPH_AVAILABLE = False
    print("警告: pymorphy3 库未安装，形态学分析功能不可用")

# ========== 全局配置 ==========
AUDIO_FILE_PATH = os.path.join(os.path.expanduser("~"), "Downloads", "clipboard_speech.mp3")
# 支付宝收款码图片路径
ALIPAY_QRCODE_PATH = "IMG_3693.PNG"
# 公众号二维码图片路径
WECHAT_QRCODE_PATH = "qrcode_for_gh_fc4e072e1747_258.jpg"
# 单词历史文件路径
WORD_HISTORY_PATH = os.path.join(os.path.expanduser("~"), "Downloads", "russian_word_history.pkl")

# 抑制警告
warnings.filterwarnings("ignore", category=UserWarning)

# 形态学分析相关配置
GRAM_MAP = {
    "NOUN": "名词",
    "NPRO": "代词",
    "VERB": "动词",
    "INFN": "不定式",
    "ADJF": "形容词（长形式）",
    "ADJS": "形容词（短形式）",
    "PRTF": "分词（长形式）",
    "PRTS": "分词（短形式）",
    "GRND": "副动词",
    "ADVB": "副词",
    "NUMR": "数词",
    "PREP": "介词",
    "CONJ": "连词",
    "PRCL": "语气词",
    "INTJ": "感叹词",
    "masc": "阳性",
    "femn": "阴性",
    "neut": "中性",
    "sing": "单数",
    "plur": "复数",
    "nomn": "主格",
    "gent": "属格",
    "datv": "与格",
    "accs": "宾格",
    "ablt": "工具格",
    "loct": "前置格",
    "voct": "呼格",
    "past": "过去时",
    "pres": "现在时",
    "futr": "将来时",
    "perf": "完成体",
    "impf": "未完成体",
    "indc": "陈述式",
    "impr": "祈使式",
    "1per": "第一人称",
    "2per": "第二人称",
    "3per": "第三人称",
    "tran": "及物",
    "intr": "不及物",
    "anim": "有生",
    "inan": "无生",
    "Anph": "回指代词",
    "Demn": "指示代词",
    "Ques": "疑问代词",
    "Rel": "关系代词",
    "Poss": "物主代词",
    "Pers": "人称代词",
}

class WorkerThread(QThread):
    """工作线程，用于在后台运行剪贴板监控"""
    
    # 定义信号
    log_signal = Signal(str, str)  # 消息, 类型(info/warning/error/success)
    status_signal = Signal(str)  # 状态更新
    processed_count_signal = Signal(int)  # 处理计数更新
    result_signal = Signal(str, str, str, str)  # 原始文本, 重音标注, 翻译, 形态学分析
    word_analysis_signal = Signal(list)  # 单词分析结果（新增）
    
    def __init__(self):
        super().__init__()
        self.is_running = False
        self.is_processing = False
        
        # 配置参数
        self.play_times = 3  # 修改：默认朗读次数改为3次
        self.play_interval = 0.3  # 朗读时间间隔（新增）
        self.check_interval = 0.5
        self.process_cooldown = 1.0
        self.audio_gain_db = 0
        
        # 功能开关
        self.stress_mark_enabled = True
        self.translation_enabled = True
        self.morphology_enabled = True
        
        # 工具实例
        self.normalizer = None
        self.translator = None
        self.morph_analyzer = None
        
        # 状态变量
        self.last_content = ""
        self.last_process_time = 0
        self.processed_count = 0
        
        # 单词分析结果存储（新增）
        self.word_analysis_results = []
        
        # 初始化工具
        self.init_tools()
    
    def init_tools(self):
        """初始化重音标注、翻译和形态学分析工具"""
        # 初始化重音标注器
        if self.stress_mark_enabled:
            try:
                from tsnorm import Normalizer
                self.normalizer = Normalizer(
                    stress_mark=chr(0x301),
                    stress_mark_pos="after"
                )
                self.log_signal.emit("✅ tsnorm库加载成功，重音标注功能已启用", "success")
            except ImportError:
                self.log_signal.emit("⚠️ tsnorm库未安装，跳过重音标注功能", "warning")
            except Exception as e:
                self.log_signal.emit(f"⚠️ 初始化重音标注器时出错: {e}", "warning")
        
        # 初始化翻译器
        if self.translation_enabled:
            try:
                from deep_translator import GoogleTranslator
                self.translator = GoogleTranslator(source="ru", target="zh-CN")
                self.log_signal.emit("✅ 翻译库加载成功，翻译功能已启用", "success")
            except ImportError:
                self.log_signal.emit("⚠️ deep_translator库未安装，跳过翻译功能", "warning")
            except Exception as e:
                self.log_signal.emit(f"⚠️ 初始化翻译器时出错: {e}", "warning")
        
        # 初始化形态学分析器
        if self.morphology_enabled and MORPH_AVAILABLE:
            try:
                self.morph_analyzer = pymorphy3.MorphAnalyzer()
                self.log_signal.emit("✅ pymorphy3库加载成功，形态学分析功能已启用", "success")
            except Exception as e:
                self.log_signal.emit(f"⚠️ 初始化形态学分析器时出错: {e}", "warning")
        elif self.morphology_enabled and not MORPH_AVAILABLE:
            self.log_signal.emit("⚠️ pymorphy3库未安装，跳过形态学分析功能", "warning")
    
    def set_parameters(self, play_times, play_interval, check_interval, process_cooldown, audio_gain_db, 
                       stress_enabled, translation_enabled, morphology_enabled):
        """设置工作参数"""
        self.play_times = play_times
        self.play_interval = play_interval  # 新增：朗读时间间隔
        self.check_interval = check_interval
        self.process_cooldown = process_cooldown
        self.audio_gain_db = audio_gain_db
        self.stress_mark_enabled = stress_enabled
        self.translation_enabled = translation_enabled
        self.morphology_enabled = morphology_enabled
        
        # 重新初始化工具以反映设置更改
        self.init_tools()
        
        # 日志输出参数设置
        self.log_signal.emit(f"✅ 参数已更新: 朗读{play_times}遍, 间隔{play_interval}秒", "info")
    
    def is_russian_text(self, text):
        """判断文本是否为俄语（基于西里尔字母比例）"""
        if not text or not text.strip():
            return False
        
        # 查找西里尔字母
        russian_chars = re.findall(r'[\u0400-\u04FF]', text)
        # 查找所有字母（排除数字、空格、标点）
        total_letters = re.findall(r'[^\s\d\W]', text)
        
        if not total_letters:
            return False
        
        # 如果西里尔字母占比超过50%，则认为是俄语
        return (len(russian_chars) / len(total_letters)) > 0.5
    
    def add_stress_marks(self, text):
        """为俄语文本添加重音标记"""
        if not self.stress_mark_enabled or not self.normalizer:
            return text, False
        
        try:
            normalized_text = self.normalizer(text)
            return normalized_text, True
        except Exception as e:
            self.log_signal.emit(f"⚠️ 重音标注失败: {e}", "warning")
            return text, False
    
    def translate_russian(self, text):
        """将俄语文本翻译成中文"""
        if not self.translation_enabled or not self.translator:
            return "", False
        
        try:
            # 如果文本太长，进行截断（Google翻译有长度限制）
            if len(text) > 5000:
                text_to_translate = text[:5000] + "..."
            else:
                text_to_translate = text
            
            translated_text = self.translator.translate(text_to_translate)
            return translated_text, True
        except Exception as e:
            self.log_signal.emit(f"⚠️ 翻译失败: {e}", "warning")
            return "", False
    
    def tag_to_cn(self, tag):
        """将俄语语法标签转换为中文描述"""
        try:
            # 使用tag对象的grammemes属性
            grammemes = tag.grammemes
            cn_parts = []
            for g in grammemes:
                # 有些特征可能是组合形式，如"Anph sing"，需要进一步拆分
                if ' ' in g:
                    sub_parts = g.split(' ')
                    for sub_g in sub_parts:
                        cn_parts.append(GRAM_MAP.get(sub_g, sub_g))
                else:
                    cn_parts.append(GRAM_MAP.get(g, g))
            return "，".join(cn_parts)
        except Exception as e:
            return f"解析错误: {str(e)}"
    
    def morphological_analysis(self, text):
        """对俄语文本进行形态学分析"""
        if not self.morphology_enabled or not self.morph_analyzer:
            return "", False, []
        
        try:
            # 提取俄语单词
            words = re.findall(r"[А-Яа-яЁё]+", text)
            if not words:
                return "未找到俄语单词", False, []
            
            result_lines = []
            word_analysis = []  # 存储单词分析结果（新增）
            
            for word in words:
                # 获取第一个（最可能的）分析结果
                parsed = self.morph_analyzer.parse(word)[0]
                normal_form = parsed.normal_form
                tag_cn = self.tag_to_cn(parsed.tag)
                
                # 修改：直接显示原形和语法标签，不显示原始单词
                result_lines.append(f"{word}({tag_cn}) →【原形】 {normal_form}")
                
                # 存储单词分析结果（新增）
                word_analysis.append({
                    'original': word,
                    'normal_form': normal_form,
                    'tag_cn': tag_cn
                })
            
            return "\n".join(result_lines), True, word_analysis
        except Exception as e:
            error_msg = f"形态学分析失败: {str(e)}"
            self.log_signal.emit(f"⚠️ {error_msg}", "warning")
            return error_msg, False, []
    
    def text_to_speech_russian(self, text):
        """生成俄语语音，并独立增强音频文件本身的音量"""
        try:
            # 1. 添加重音标记（如果可用）
            text_with_stress, stress_added = self.add_stress_marks(text)
            
            # 2. 翻译文本（如果可用）
            translated_text, translation_success = self.translate_russian(text)
            
            # 3. 形态学分析（如果可用）
            morphological_result, morph_success, word_analysis = self.morphological_analysis(text)
            
            # 发送结果到GUI
            self.result_signal.emit(text, 
                                   text_with_stress if stress_added else "", 
                                   translated_text if translation_success else "",
                                   morphological_result if morph_success else "")
            
            # 存储单词分析结果（新增）
            self.word_analysis_results = word_analysis
            
            # 发送单词分析结果信号（新增）
            translated_words = []
            if word_analysis and self.translator:
                # 尝试翻译每个单词的原形
                for word_info in word_analysis:
                    try:
                        # 翻译单词原形
                        word_translation = self.translator.translate(word_info['normal_form'])
                        translated_words.append((word_info['normal_form'], word_translation))
                        
                        # 在日志中显示单词翻译（新增）
                        self.log_signal.emit(f"单词翻译: {word_info['original']} → {word_info['normal_form']} → {word_translation}", "info")
                    except Exception as e:
                        self.log_signal.emit(f"⚠️ 单词 '{word_info['normal_form']}' 翻译失败: {e}", "warning")
                        translated_words.append((word_info['normal_form'], "翻译失败"))
            
            # 发送单词分析结果
            self.word_analysis_signal.emit(translated_words)
            
            # 4. 生成原始音频到临时文件
            tts = gTTS(text=text_with_stress, lang='ru', slow=False)
            temp_path = AUDIO_FILE_PATH.replace('.mp3', '_temp.mp3')
            tts.save(temp_path)

            # 5. 加载、增强并标准化音频
            audio = AudioSegment.from_file(temp_path, format="mp3")
            louder_audio = audio + self.audio_gain_db
            normalized_audio = louder_audio.normalize()
            normalized_audio.export(AUDIO_FILE_PATH, format="mp3")

            # 6. 清理临时文件
            if os.path.exists(temp_path):
                os.remove(temp_path)
            
            return True, stress_added
        except Exception as e:
            # 增强失败时的回退方案
            try:
                self.log_signal.emit(f"⚠️ 音频增强失败，回退到原始音频: {e}", "warning")
                tts = gTTS(text=text, lang='ru', slow=False)
                tts.save(AUDIO_FILE_PATH)
                return True, False
            except:
                self.log_signal.emit(f"❌ 语音合成失败: {e}", "error")
                return False, False
    
    def play_audio(self):
        """播放音频（使用自定义的朗读时间间隔）"""
        try:
            # 播放已增强的音频（循环播放）
            for i in range(self.play_times):
                self.log_signal.emit(f"开始播放俄语语音 (第 {i+1}/{self.play_times} 遍, 间隔 {self.play_interval}秒)...", "info")
                
                # 根据平台选择播放命令
                if sys.platform == "darwin":  # macOS
                    result = subprocess.run(['afplay', AUDIO_FILE_PATH],
                                          capture_output=True, text=True)
                elif sys.platform == "win32":  # Windows
                    result = subprocess.run(['cmd', '/c', 'start', '/wait', AUDIO_FILE_PATH],
                                          capture_output=True, text=True, shell=True)
                else:  # Linux
                    result = subprocess.run(['mpg123', AUDIO_FILE_PATH],
                                          capture_output=True, text=True)
                
                # 如果不是最后一次播放，等待用户自定义的时间间隔
                if i < self.play_times - 1:
                    time.sleep(self.play_interval)  # 使用用户设置的间隔
            
            if result.returncode == 0:
                self.log_signal.emit(f"播放完成 (共播放 {self.play_times} 遍, 间隔 {self.play_interval}秒)", "info")
                return True, None
            else:
                self.log_signal.emit(f"❌ 播放失败: {result.stderr}", "error")
                return False, result.stderr
        except Exception as e:
            self.log_signal.emit(f"❌ 播放过程中出错: {e}", "error")
            return False, str(e)
    
    def run(self):
        """主监控循环（在线程中运行）"""
        self.is_running = True
        self.log_signal.emit("🎧 剪贴板监控已启动", "success")
        self.status_signal.emit("监控中...")
        
        try:
            while self.is_running:
                if self.is_processing:
                    time.sleep(self.check_interval)
                    continue
                
                current_content = pyperclip.paste()
                current_time = time.time()
                
                # 检查是否有实际内容且不是空字符串
                if (current_content and 
                    current_content != self.last_content and 
                    current_content.strip() != "" and
                    (current_time - self.last_process_time) >= self.process_cooldown):
                    
                    # 标记为正在处理
                    self.is_processing = True
                    self.last_content = current_content
                    self.last_process_time = current_time
                    
                    if self.is_russian_text(current_content):
                        self.processed_count += 1
                        self.processed_count_signal.emit(self.processed_count)
                        
                        # 显示检测到的文本前100个字符（修改：在日志中显示检测到的俄语文本）
                        display_text = current_content[:100] + ("..." if len(current_content) > 100 else "")
                        self.log_signal.emit(f"📥 检测到俄语文本: {display_text}", "info")
                        
                        # 生成语音
                        success, _ = self.text_to_speech_russian(current_content)
                        
                        # 播放语音
                        if success:
                            play_success, error_message = self.play_audio()
                            if not play_success:
                                self.log_signal.emit(f"❌ 语音播放失败: {error_message}", "error")
                        else:
                            self.log_signal.emit("❌ 语音生成失败，跳过播放", "error")
                    else:
                        # 非俄语文本
                        time.sleep(0.2)
                    
                    # 处理完成
                    self.is_processing = False
                
                time.sleep(self.check_interval)
        
        except Exception as e:
            self.log_signal.emit(f"❌ 监控过程中出现未预期的错误: {e}", "error")
        finally:
            self.status_signal.emit("已停止")
            self.log_signal.emit("监控已停止", "info")
    
    def stop(self):
        """停止监控"""
        self.is_running = False

class MainWindow(QMainWindow):
    """主窗口"""
    
    def __init__(self):
        super().__init__()
        self.worker_thread = None
        self.word_translations = []
        self.word_history = OrderedDict()  # 用于存储所有单词历史
        self.log_messages = []  # 存储日志消息用于提取单词
        
        # 设置程序图标
        self.set_window_icon()
    
        # 先初始化UI
        self.init_ui()
        
        # 然后加载历史单词（此时UI已初始化）
        self.load_word_history()
        
        # 最后检查依赖
        self.check_dependencies()
    
    def load_word_history(self):
        """加载历史单词记录"""
        try:
            if os.path.exists(WORD_HISTORY_PATH):
                with open(WORD_HISTORY_PATH, 'rb') as f:
                    self.word_history = pickle.load(f)
                # 更新单词计数显示
                self.word_count_label.setText(f"单词库: {len(self.word_history)} 个")
                self.log_message(f"✅ 已加载历史单词记录，共 {len(self.word_history)} 个单词", "success")
            else:
                self.log_message("ℹ️ 没有找到历史单词记录文件，将创建新的单词库", "info")
        except Exception as e:
            self.log_message(f"⚠️ 加载历史单词记录失败: {e}", "warning")
            self.word_history = OrderedDict()
    
    def save_word_history(self):
        """保存历史单词记录"""
        try:
            with open(WORD_HISTORY_PATH, 'wb') as f:
                pickle.dump(self.word_history, f)
            # 不在UI初始化时记录日志
            if hasattr(self, 'log_text'):
                self.log_message("✅ 历史单词记录已保存", "info")
        except Exception as e:
            # 不在UI初始化时记录日志
            if hasattr(self, 'log_text'):
                self.log_message(f"⚠️ 保存历史单词记录失败: {e}", "warning")
    
    def add_word_to_history(self, word, translation):
        """添加单词到历史记录"""
        if word and translation and translation != "翻译失败":
            # 只保留原形，去除重复
            self.word_history[word] = translation
            self.save_word_history()
    
    def set_window_icon(self):
        """设置程序窗口图标"""
        icon_paths = [
            "/Users/hebin/Downloads/俄语tts/pyc.jpg",  # 用户提供的路径
            "pyc.jpg",  # 当前目录下的相对路径
            "icon.png",  # 备用图标
            "icon.ico"   # Windows图标格式
        ]
    
        for icon_path in icon_paths:
            if os.path.exists(icon_path):
                try:
                    pixmap = QPixmap(icon_path)
                    if not pixmap.isNull():
                        icon = QIcon(pixmap)
                        self.setWindowIcon(icon)
                        print(f"✅ 程序图标已设置: {icon_path}")
                        return True
                except Exception as e:
                    print(f"⚠️ 加载图标失败 {icon_path}: {e}")
    
        print("⚠️ 未找到可用的图标文件，使用默认图标")
        return False
    
    def create_scrollable_tab(self, widget, layout):
        """创建一个可滚动的标签页"""
        # 创建滚动区域
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        
        # 设置内部widget
        widget.setLayout(layout)
        scroll_area.setWidget(widget)
        
        return scroll_area
    
    def init_ui(self):
        """初始化UI界面"""
        # 修改：窗口标题体现特色
        self.setWindowTitle("俄语剪贴板朗读器 - 重音标注+形态学分析版")
        self.setGeometry(300, 200, 1000, 800)  # 增加窗口大小
        
        # 创建中心部件
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        # 主布局
        main_layout = QVBoxLayout(central_widget)
        
        # 1. 标题区域
        # 修改：主标题体现特色
        title_label = QLabel("俄语剪贴板朗读器 - 重音标注+形态学分析版")
        title_font = QFont()
        title_font.setPointSize(16)
        title_font.setBold(True)
        title_label.setFont(title_font)
        title_label.setAlignment(Qt.AlignCenter)
        title_label.setStyleSheet("padding: 10px; background-color: #f0f0f0; border-radius: 5px;")
        main_layout.addWidget(title_label)
        
        
        # 2. 标签页
        tab_widget = QTabWidget()
        tab_widget.setMinimumSize(800, 600)  # 设置最小大小
        main_layout.addWidget(tab_widget)
        
        # 标签1：控制面板
        control_widget = QWidget()
        control_layout = QVBoxLayout()
        
        # 参数设置组
        params_group = QGroupBox("参数设置")
        params_layout = QVBoxLayout()
        
        # 朗读次数
        times_layout = QHBoxLayout()
        times_layout.addWidget(QLabel("朗读次数:"))
        self.times_spin = QSpinBox()
        self.times_spin.setRange(1, 20)
        self.times_spin.setValue(3)  # 修改：默认朗读次数改为3次
        self.times_spin.setToolTip("每段文本朗读的次数")
        times_layout.addWidget(self.times_spin)
        times_layout.addStretch()
        params_layout.addLayout(times_layout)
        
        # 朗读时间间隔（新增）
        play_interval_layout = QHBoxLayout()
        play_interval_layout.addWidget(QLabel("朗读间隔(秒):"))
        self.play_interval_spin = QDoubleSpinBox()
        self.play_interval_spin.setRange(0.1, 5.0)
        self.play_interval_spin.setValue(0.3)
        self.play_interval_spin.setSingleStep(0.1)
        self.play_interval_spin.setToolTip("每遍朗读之间的间隔时间")
        play_interval_layout.addWidget(self.play_interval_spin)
        play_interval_layout.addStretch()
        params_layout.addLayout(play_interval_layout)
        
        # 检查间隔
        interval_layout = QHBoxLayout()
        interval_layout.addWidget(QLabel("检查间隔(秒):"))
        self.interval_spin = QDoubleSpinBox()
        self.interval_spin.setRange(0.1, 5.0)
        self.interval_spin.setValue(0.5)
        self.interval_spin.setSingleStep(0.1)
        self.interval_spin.setToolTip("检查剪贴板的时间间隔")
        interval_layout.addWidget(self.interval_spin)
        interval_layout.addStretch()
        params_layout.addLayout(interval_layout)
        
        # 冷却时间
        cooldown_layout = QHBoxLayout()
        cooldown_layout.addWidget(QLabel("冷却时间(秒):"))
        self.cooldown_spin = QDoubleSpinBox()
        self.cooldown_spin.setRange(0.1, 10.0)
        self.cooldown_spin.setValue(1.0)
        self.cooldown_spin.setSingleStep(0.1)
        self.cooldown_spin.setToolTip("处理相同内容后的冷却时间（防重复触发）")
        cooldown_layout.addWidget(self.cooldown_spin)
        cooldown_layout.addStretch()
        params_layout.addLayout(cooldown_layout)
        
        # 音频增益
        gain_layout = QHBoxLayout()
        gain_layout.addWidget(QLabel("音频增益(dB):"))
        self.gain_spin = QSpinBox()
        self.gain_spin.setRange(-10, 20)
        self.gain_spin.setValue(0)
        self.gain_spin.setToolTip("音频增强，正数增加音量，负数减小音量")
        gain_layout.addWidget(self.gain_spin)
        gain_layout.addStretch()
        params_layout.addLayout(gain_layout)
        
        # 功能开关
        self.stress_check = QCheckBox("启用重音标注")
        self.stress_check.setChecked(True)
        params_layout.addWidget(self.stress_check)
        
        self.translation_check = QCheckBox("启用中文翻译")
        self.translation_check.setChecked(True)
        params_layout.addWidget(self.translation_check)
        
        self.morphology_check = QCheckBox("启用形态学分析")
        self.morphology_check.setChecked(True)
        self.morphology_check.setToolTip("对俄语单词进行词性、格、数等语法分析")
        params_layout.addWidget(self.morphology_check)
        
        params_group.setLayout(params_layout)
        control_layout.addWidget(params_group)
        
        # 时间参数说明
        time_info_frame = QFrame()
        time_info_frame.setFrameShape(QFrame.StyledPanel)
        time_info_frame.setStyleSheet("background-color: #f9f9f9; border: 1px solid #ddd; border-radius: 5px; padding: 8px;")
        time_info_layout = QVBoxLayout(time_info_frame)
        
        time_info_label = QLabel("⏱️ 时间参数说明：")
        time_info_label.setStyleSheet("font-weight: bold; color: #333;")
        time_info_layout.addWidget(time_info_label)
        
        # 创建说明文本
        explanation_text = """
        • <b>朗读间隔</b>: 每遍朗读之间的等待时间<br>
        • <b>检查间隔</b>: 检查剪贴板的频率<br>
        • <b>冷却时间</b>: 处理完一段文本后，防止重复触发的等待时间
        """
        
        explanation_label = QLabel(explanation_text)
        explanation_label.setStyleSheet("color: #666; font-size: 10pt;")
        explanation_label.setWordWrap(True)
        time_info_layout.addWidget(explanation_label)
        
        control_layout.addWidget(time_info_frame)
        
        # 控制按钮
        button_layout = QHBoxLayout()
        
        self.start_btn = QPushButton("开始监控")
        self.start_btn.setStyleSheet("background-color: #4CAF50; color: white; padding: 8px; font-weight: bold;")
        self.start_btn.clicked.connect(self.start_monitoring)
        button_layout.addWidget(self.start_btn)
        
        self.stop_btn = QPushButton("停止监控")
        self.stop_btn.setStyleSheet("background-color: #f44336; color: white; padding: 8px;")
        self.stop_btn.setEnabled(False)
        self.stop_btn.clicked.connect(self.stop_monitoring)
        button_layout.addWidget(self.stop_btn)
        
        control_layout.addLayout(button_layout)
        
        # 状态信息
        status_layout = QHBoxLayout()
        status_layout.addWidget(QLabel("状态:"))
        self.status_label = QLabel("就绪")
        self.status_label.setStyleSheet("font-weight: bold; color: #666;")
        status_layout.addWidget(self.status_label)
        
        status_layout.addStretch()
        
        status_layout.addWidget(QLabel("已处理:"))
        self.count_label = QLabel("0 次")
        self.count_label.setStyleSheet("font-weight: bold; color: #2196F3;")
        status_layout.addWidget(self.count_label)
        
        status_layout.addStretch()
        
        # 显示单词库数量
        self.word_count_label = QLabel(f"单词库: {len(self.word_history)} 个")
        self.word_count_label.setStyleSheet("font-weight: bold; color: #FF9800;")
        status_layout.addWidget(self.word_count_label)
        
        status_layout.addStretch()
        
        # 显示当前朗读间隔
        self.interval_status_label = QLabel(f"朗读间隔: {self.play_interval_spin.value()}秒")
        self.interval_status_label.setStyleSheet("font-weight: bold; color: #9C27B0;")
        status_layout.addWidget(self.interval_status_label)
        
        control_layout.addLayout(status_layout)
        control_layout.addStretch()
        
        # 创建滚动区域并添加到标签页
        control_scroll = self.create_scrollable_tab(control_widget, control_layout)
        tab_widget.addTab(control_scroll, "控制")
        
        # 标签2：结果显示
        result_widget = QWidget()
        result_layout = QVBoxLayout()
        
        # 原始文本
        original_group = QGroupBox("原始文本")
        original_layout = QVBoxLayout()
        self.original_text = QTextEdit()
        self.original_text.setReadOnly(True)
        self.original_text.setMinimumHeight(100)
        self.original_text.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        original_layout.addWidget(self.original_text)
        original_group.setLayout(original_layout)
        result_layout.addWidget(original_group)
        
        # 重音标注
        stress_group = QGroupBox("重音标注")
        stress_layout = QVBoxLayout()
        self.stress_text = QTextEdit()
        self.stress_text.setReadOnly(True)
        self.stress_text.setMinimumHeight(100)
        self.stress_text.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        stress_layout.addWidget(self.stress_text)
        stress_group.setLayout(stress_layout)
        result_layout.addWidget(stress_group)
        
        # 中文翻译
        translation_group = QGroupBox("中文翻译")
        translation_layout = QVBoxLayout()
        self.translation_text = QTextEdit()
        self.translation_text.setReadOnly(True)
        self.translation_text.setMinimumHeight(100)
        self.translation_text.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        translation_layout.addWidget(self.translation_text)
        translation_group.setLayout(translation_layout)
        result_layout.addWidget(translation_group)
        
        # 形态学分析（新增）
        morphology_group = QGroupBox("形态学分析")
        morphology_layout = QVBoxLayout()
        self.morphology_text = QTextEdit()
        self.morphology_text.setReadOnly(True)
        self.morphology_text.setMinimumHeight(150)
        self.morphology_text.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        morphology_layout.addWidget(self.morphology_text)
        morphology_group.setLayout(morphology_layout)
        result_layout.addWidget(morphology_group)
        
        # 添加弹性空间
        result_layout.addStretch()
        
        # 创建滚动区域并添加到标签页
        result_scroll = self.create_scrollable_tab(result_widget, result_layout)
        tab_widget.addTab(result_scroll, "结果")
        
        # 标签3：日志
        log_widget = QWidget()
        log_layout = QVBoxLayout()
        
        # 日志工具栏
        log_toolbar = QHBoxLayout()
        
        self.clear_log_btn = QPushButton("清空日志")
        self.clear_log_btn.clicked.connect(self.clear_log)
        log_toolbar.addWidget(self.clear_log_btn)
        
        self.save_log_btn = QPushButton("保存日志")
        self.save_log_btn.clicked.connect(self.save_log)
        log_toolbar.addWidget(self.save_log_btn)
        
        # 导出单词卡按钮 - 增强功能
        self.export_words_btn = QPushButton("导出单词卡")
        self.export_words_btn.setStyleSheet("background-color: #9C27B0; color: white; padding: 8px;")
        self.export_words_btn.clicked.connect(self.show_export_options)
        self.export_words_btn.setToolTip("导出单词原形和中文翻译为TXT文件")
        log_toolbar.addWidget(self.export_words_btn)
        
        # 清空单词库按钮
        self.clear_words_btn = QPushButton("清空单词库")
        self.clear_words_btn.setStyleSheet("background-color: #FF5722; color: white; padding: 8px;")
        self.clear_words_btn.clicked.connect(self.clear_word_history)
        self.clear_words_btn.setToolTip("清空所有历史单词记录")
        log_toolbar.addWidget(self.clear_words_btn)
        
        log_toolbar.addStretch()
        
        log_layout.addLayout(log_toolbar)
        
        # 日志显示
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self.log_text.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        log_layout.addWidget(self.log_text)
        
        # 创建滚动区域并添加到标签页
        log_scroll = self.create_scrollable_tab(log_widget, log_layout)
        tab_widget.addTab(log_scroll, "日志")
        
        # 标签4：捐赠
        donation_widget = QWidget()
        donation_layout = QVBoxLayout()
        
        # 捐赠标题
        donation_title = QLabel("❤️ 支持开发者")
        donation_title_font = QFont()
        donation_title_font.setPointSize(18)
        donation_title_font.setBold(True)
        donation_title.setFont(donation_title_font)
        donation_title.setAlignment(Qt.AlignCenter)
        donation_title.setStyleSheet("padding: 15px; color: #e91e63;")
        donation_layout.addWidget(donation_title)
        
        # 感谢信息
        thanks_label = QLabel("感谢您使用俄语剪贴板朗读器！")
        thanks_label.setAlignment(Qt.AlignCenter)
        thanks_label.setStyleSheet("font-size: 14pt; padding: 10px; color: #333;")
        donation_layout.addWidget(thanks_label)
        
        # 捐赠说明
        donation_info = QLabel("""
        <div style='text-align: center;'>
        <p>如果这个程序对您的俄语学习有所帮助，您可以考虑支持开发者。</p>
        <p>您的支持将帮助我继续开发和维护这个项目，添加更多有用的功能。</p>
        <p>非常感谢您的慷慨！ 🙏</p>
        </div>
        """)
        donation_info.setAlignment(Qt.AlignCenter)
        donation_info.setStyleSheet("font-size: 12pt; color: #555; padding: 10px;")
        donation_info.setWordWrap(True)
        donation_layout.addWidget(donation_info)
        
        # 支付宝收款码
        alipay_frame = QFrame()
        alipay_frame.setFrameShape(QFrame.StyledPanel)
        alipay_frame.setStyleSheet("background-color: #f5f5f5; border: 2px solid #ddd; border-radius: 10px; padding: 15px;")
        alipay_layout = QVBoxLayout(alipay_frame)
        
        alipay_label = QLabel("支付宝收款码")
        alipay_label.setAlignment(Qt.AlignCenter)
        alipay_label.setStyleSheet("font-size: 16pt; font-weight: bold; color: #00a1e9; padding: 10px;")
        alipay_layout.addWidget(alipay_label)
        
        # 加载支付宝图片
        self.alipay_image_label = QLabel()
        self.alipay_image_label.setAlignment(Qt.AlignCenter)
        
        # 尝试加载图片
        if os.path.exists(ALIPAY_QRCODE_PATH):
            pixmap = QPixmap(ALIPAY_QRCODE_PATH)
            if not pixmap.isNull():
                # 缩放图片以适应界面
                scaled_pixmap = pixmap.scaled(300, 300, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                self.alipay_image_label.setPixmap(scaled_pixmap)
                self.alipay_image_label.setStyleSheet("border: 1px solid #ccc; border-radius: 5px; padding: 5px;")
            else:
                self.alipay_image_label.setText("❌ 无法加载图片文件")
                self.alipay_image_label.setStyleSheet("color: #ff4444; font-size: 12pt; padding: 20px;")
        else:
            self.alipay_image_label.setText(f"❌ 图片文件不存在\n路径: {ALIPAY_QRCODE_PATH}")
            self.alipay_image_label.setStyleSheet("color: #ff4444; font-size: 10pt; padding: 20px;")
        
        alipay_layout.addWidget(self.alipay_image_label)
        
        # 支付宝使用说明
        alipay_instruction = QLabel("使用支付宝扫描上方二维码进行捐赠")
        alipay_instruction.setAlignment(Qt.AlignCenter)
        alipay_instruction.setStyleSheet("font-size: 11pt; color: #666; padding: 10px; font-style: italic;")
        alipay_layout.addWidget(alipay_instruction)
        
        donation_layout.addWidget(alipay_frame)
        
        # 其他捐赠方式
        other_methods_frame = QFrame()
        other_methods_frame.setFrameShape(QFrame.StyledPanel)
        other_methods_frame.setStyleSheet("background-color: #f9f9f9; border: 1px solid #ddd; border-radius: 8px; padding: 15px;")
        other_methods_layout = QVBoxLayout(other_methods_frame)
        
        other_methods_label = QLabel("其他支持方式")
        other_methods_label.setAlignment(Qt.AlignCenter)
        other_methods_label.setStyleSheet("font-size: 14pt; font-weight: bold; color: #333; padding: 5px;")
        other_methods_layout.addWidget(other_methods_label)
        
        other_methods_info = QLabel("""
        <ul>
        <li><b>分享给朋友</b>: 将程序分享给更多俄语学习者</li>
        <li><b>反馈建议</b>: 提出改进建议或报告问题</li>
        <li><b>参与开发</b>: 如果您是开发者，欢迎参与项目开发</li>
        </ul>
        """)
        other_methods_info.setStyleSheet("font-size: 11pt; color: #555; padding: 10px;")
        other_methods_info.setWordWrap(True)
        other_methods_layout.addWidget(other_methods_info)
        
        donation_layout.addWidget(other_methods_frame)
        
        # 底部感谢语
        final_thanks = QLabel("再次感谢您的支持！ 💝")
        final_thanks.setAlignment(Qt.AlignCenter)
        final_thanks.setStyleSheet("font-size: 13pt; font-weight: bold; color: #e91e63; padding: 15px;")
        donation_layout.addWidget(final_thanks)
        
        # 添加弹性空间
        donation_layout.addStretch()
        
        # 创建滚动区域并添加到标签页
        donation_scroll = self.create_scrollable_tab(donation_widget, donation_layout)
        tab_widget.addTab(donation_scroll, "捐赠")
        
        # 标签5：联系我们（新增）
        contact_widget = QWidget()
        contact_layout = QVBoxLayout()
        
        # 联系标题
        contact_title = QLabel("📧 联系我们")
        contact_title_font = QFont()
        contact_title_font.setPointSize(18)
        contact_title_font.setBold(True)
        contact_title.setFont(contact_title_font)
        contact_title.setAlignment(Qt.AlignCenter)
        contact_title.setStyleSheet("padding: 15px; color: #2196F3;")
        contact_layout.addWidget(contact_title)
        
        # 联系说明
        contact_desc = QLabel("""
        <div style='text-align: center;'>
        <p>如果您在使用过程中遇到任何问题，或者有功能建议，欢迎联系我们！</p>
        <p>我们非常重视您的反馈，这有助于我们改进产品。</p>
        </div>
        """)
        contact_desc.setAlignment(Qt.AlignCenter)
        contact_desc.setStyleSheet("font-size: 12pt; color: #555; padding: 10px;")
        contact_desc.setWordWrap(True)
        contact_layout.addWidget(contact_desc)
        
        # 使用网格布局来并排显示二维码和联系方式
        contact_grid = QGridLayout()
        contact_grid.setSpacing(20)
        
        # 左侧：公众号二维码
        wechat_frame = QFrame()
        wechat_frame.setFrameShape(QFrame.StyledPanel)
        wechat_frame.setStyleSheet("background-color: #f5f5f5; border: 2px solid #4CAF50; border-radius: 10px; padding: 15px;")
        wechat_layout = QVBoxLayout(wechat_frame)
        
        wechat_label = QLabel("微信公众号")
        wechat_label.setAlignment(Qt.AlignCenter)
        wechat_label.setStyleSheet("font-size: 16pt; font-weight: bold; color: #4CAF50; padding: 10px;")
        wechat_layout.addWidget(wechat_label)
        
        # 加载微信公众号图片
        self.wechat_image_label = QLabel()
        self.wechat_image_label.setAlignment(Qt.AlignCenter)
        
        # 尝试加载图片
        if os.path.exists(WECHAT_QRCODE_PATH):
            pixmap = QPixmap(WECHAT_QRCODE_PATH)
            if not pixmap.isNull():
                # 缩放图片以适应界面
                scaled_pixmap = pixmap.scaled(250, 250, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                self.wechat_image_label.setPixmap(scaled_pixmap)
                self.wechat_image_label.setStyleSheet("border: 1px solid #ccc; border-radius: 5px; padding: 5px;")
            else:
                self.wechat_image_label.setText("❌ 无法加载图片文件")
                self.wechat_image_label.setStyleSheet("color: #ff4444; font-size: 12pt; padding: 20px;")
        else:
            self.wechat_image_label.setText(f"❌ 图片文件不存在\n路径: {WECHAT_QRCODE_PATH}")
            self.wechat_image_label.setStyleSheet("color: #ff4444; font-size: 10pt; padding: 20px;")
        
        wechat_layout.addWidget(self.wechat_image_label)
        
        # 微信公众号使用说明
        wechat_instruction = QLabel("扫描关注公众号\n获取最新更新和教程")
        wechat_instruction.setAlignment(Qt.AlignCenter)
        wechat_instruction.setStyleSheet("font-size: 11pt; color: #666; padding: 10px;")
        wechat_instruction.setWordWrap(True)
        wechat_layout.addWidget(wechat_instruction)
        
        # 右侧：邮箱和其他联系方式
        email_frame = QFrame()
        email_frame.setFrameShape(QFrame.StyledPanel)
        email_frame.setStyleSheet("background-color: #f5f5f5; border: 2px solid #FF9800; border-radius: 10px; padding: 15px;")
        email_layout = QVBoxLayout(email_frame)
        
        email_label = QLabel("📩 邮箱联系")
        email_label.setAlignment(Qt.AlignCenter)
        email_label.setStyleSheet("font-size: 16pt; font-weight: bold; color: #FF9800; padding: 10px;")
        email_layout.addWidget(email_label)
        
        # 邮箱信息
        email_info = QLabel("""
        <div style='text-align: left;'>
        <p><b>开发者邮箱:</b></p>
        <p style='font-family: monospace; font-size: 14pt; background-color: #fff8e1; padding: 10px; border-radius: 5px;'>
        binhe9301@gmail.com
        </p>
        
        <p><b>联系事项:</b></p>
        <ul>
        <li>功能建议和需求</li>
        <li>错误报告和问题反馈</li>
        <li>合作与技术支持</li>
        <li>其他相关事宜</li>
        </ul>
        
        <p><b>响应时间:</b></p>
        <p>我们通常在1-3个工作日内回复邮件。</p>
        
        <p><b>其他渠道:</b></p>
        <p>您也可以通过GitHub Issues提交问题或建议。</p>
        </div>
        """)
        email_info.setStyleSheet("font-size: 11pt; color: #555; padding: 10px;")
        email_info.setWordWrap(True)
        email_layout.addWidget(email_info)
        
        # 将左右两部分添加到网格布局
        contact_grid.addWidget(wechat_frame, 0, 0)
        contact_grid.addWidget(email_frame, 0, 1)
        
        # 添加到主布局
        contact_layout.addLayout(contact_grid)
        
        # 反馈说明
        feedback_frame = QFrame()
        feedback_frame.setFrameShape(QFrame.StyledPanel)
        feedback_frame.setStyleSheet("background-color: #e8f5e9; border: 1px solid #4CAF50; border-radius: 8px; padding: 12px;")
        feedback_layout = QVBoxLayout(feedback_frame)
        
        feedback_label = QLabel("💡 反馈建议")
        feedback_label.setAlignment(Qt.AlignCenter)
        feedback_label.setStyleSheet("font-size: 14pt; font-weight: bold; color: #2E7D32; padding: 5px;")
        feedback_layout.addWidget(feedback_label)
        
        feedback_info = QLabel("""
        <p>您的反馈对我们非常重要！请告诉我们：</p>
        <ul>
        <li>您最喜欢的功能是什么？</li>
        <li>您希望添加哪些新功能？</li>
        <li>您遇到了哪些问题或困难？</li>
        <li>您对界面或用户体验有什么建议？</li>
        </ul>
        """)
        feedback_info.setStyleSheet("font-size: 10pt; color: #444; padding: 5px;")
        feedback_info.setWordWrap(True)
        feedback_layout.addWidget(feedback_info)
        
        contact_layout.addWidget(feedback_frame)
        
        # 添加弹性空间
        contact_layout.addStretch()
        
        # 创建滚动区域并添加到标签页
        contact_scroll = self.create_scrollable_tab(contact_widget, contact_layout)
        tab_widget.addTab(contact_scroll, "联系我们")
        
        # 3. 底部信息
        bottom_frame = QFrame()
        bottom_frame.setFrameShape(QFrame.HLine)
        bottom_frame.setFrameShadow(QFrame.Sunken)
        main_layout.addWidget(bottom_frame)
        
        info_label = QLabel("提示: 复制俄语文本后，程序会自动朗读并显示翻译和形态学分析。调整朗读间隔可以控制每遍朗读之间的等待时间。")
        info_label.setStyleSheet("color: #666; font-style: italic; padding: 5px;")
        info_label.setAlignment(Qt.AlignCenter)
        info_label.setWordWrap(True)
        main_layout.addWidget(info_label)
        
        # 设置主布局
        main_layout.setContentsMargins(10, 10, 10, 10)
        main_layout.setSpacing(10)
        
        # 连接朗读间隔变化的信号
        self.play_interval_spin.valueChanged.connect(self.update_interval_status)
        
        # 设置窗口大小策略
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
    
    def update_interval_status(self):
        """更新朗读间隔状态显示"""
        interval_value = self.play_interval_spin.value()
        self.interval_status_label.setText(f"朗读间隔: {interval_value}秒")
    
    def check_dependencies(self):
        """检查必要的库是否已安装"""
        missing_libs = []
        
        try:
            import pyperclip
        except ImportError:
            missing_libs.append("pyperclip")
        
        try:
            from gtts import gTTS
        except ImportError:
            missing_libs.append("gTTS")
        
        try:
            from pydub import AudioSegment
        except ImportError:
            missing_libs.append("pydub")
        
        # 检查形态学分析库
        global MORPH_AVAILABLE
        if not MORPH_AVAILABLE:
            self.log_message("⚠️ pymorphy3 库未安装，形态学分析功能不可用", "warning")
            self.log_message("如需使用形态学分析功能，请运行: pip install pymorphy3", "info")
        
        if missing_libs:
            self.log_message(f"❌ 缺少必要的Python库: {', '.join(missing_libs)}", "error")
            self.log_message("请运行以下命令安装:", "info")
            self.log_message(f"  pip install {' '.join(missing_libs)}", "info")
            
            if "pydub" in missing_libs:
                self.log_message("注意: pydub 需要 ffmpeg。在macOS上，请用Homebrew安装:", "warning")
                self.log_message("  brew install ffmpeg", "info")
                self.log_message("在Windows上，请从官网下载ffmpeg并添加到PATH", "info")
        else:
            self.log_message("✅ 基础依赖库检查通过", "success")
    
    def log_message(self, message, msg_type="info"):
        """在日志区域显示消息"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        
        # 根据消息类型设置样式
        if msg_type == "error":
            color = "#ff4444"
            prefix = "[错误]"
        elif msg_type == "warning":
            color = "#ff8800"
            prefix = "[警告]"
        elif msg_type == "success":
            color = "#00aa00"
            prefix = "[成功]"
        elif msg_type == "info":
            color = "#4444ff"
            prefix = "[信息]"
        else:
            color = "#000000"
            prefix = "[消息]"
        
        # 格式化消息
        formatted_msg = f'<font color="{color}">{prefix}</font> [{timestamp}] {message}'
        
        # 添加到日志区域
        self.log_text.append(formatted_msg)
        
        # 保存到内存中用于提取单词
        plain_msg = f"{prefix} [{timestamp}] {message}"
        self.log_messages.append(plain_msg)
        
        # 自动滚动到底部
        cursor = self.log_text.textCursor()
        cursor.movePosition(QTextCursor.End)
        self.log_text.setTextCursor(cursor)
        
        # 如果是错误消息，也显示在状态栏
        if msg_type == "error":
            self.status_label.setText("错误")
            self.status_label.setStyleSheet("font-weight: bold; color: #ff4444;")
    
    def update_result(self, original, stress, translation, morphology):
        """更新结果显示"""
        self.original_text.setPlainText(original[:500] + ("..." if len(original) > 500 else ""))
        self.stress_text.setPlainText(stress[:500] + ("..." if len(stress) > 500 else ""))
        self.translation_text.setPlainText(translation[:500] + ("..." if len(translation) > 500 else ""))
        self.morphology_text.setPlainText(morphology)
    
    def update_word_analysis(self, word_translations):
        """更新单词分析结果"""
        self.word_translations = word_translations
        
        # 将单词添加到历史记录
        for word, translation in word_translations:
            self.add_word_to_history(word, translation)
        
        # 更新单词计数显示
        self.word_count_label.setText(f"单词库: {len(self.word_history)} 个")
    
    def update_status(self, status):
        """更新状态显示"""
        self.status_label.setText(status)
        if "监控" in status:
            self.status_label.setStyleSheet("font-weight: bold; color: #4CAF50;")
        elif "停止" in status:
            self.status_label.setStyleSheet("font-weight: bold; color: #f44336;")
        else:
            self.status_label.setStyleSheet("font-weight: bold; color: #666;")
    
    def update_count(self, count):
        """更新处理计数"""
        self.count_label.setText(f"{count} 次")
    
    def extract_words_from_log(self):
        """从日志中提取所有单词翻译信息"""
        words = OrderedDict()
        
        # 正则表达式匹配单词翻译行
        pattern = r'单词翻译: (.+) → (.+) → (.+)'
        
        for message in self.log_messages:
            match = re.search(pattern, message)
            if match:
                original = match.group(1)
                normal_form = match.group(2)
                translation = match.group(3)
                
                # 使用原形作为键
                if normal_form not in words:
                    words[normal_form] = translation
        
        return words
    
    def show_export_options(self):
        """显示导出选项对话框"""
        options = [
            "导出最近一次的单词",
            "导出历史所有单词",
            "导出日志中的所有单词"
        ]
        
        choice, ok = QInputDialog.getItem(
            self, "导出选项", "选择要导出的内容:", options, 0, False
        )
        
        if ok and choice:
            if choice == "导出最近一次的单词":
                self.export_recent_words()
            elif choice == "导出历史所有单词":
                self.export_all_words()
            elif choice == "导出日志中的所有单词":
                self.export_log_words()
    
    def get_save_path(self, default_filename, title="选择保存位置"):
        """获取保存路径的对话框"""
        # 设置默认保存目录
        default_dir = os.path.expanduser("~")
        
        # 弹出文件保存对话框
        file_path, _ = QFileDialog.getSaveFileName(
            self,
            title,
            os.path.join(default_dir, default_filename),
            "文本文件 (*.txt);;所有文件 (*.*)"
        )
        
        return file_path
    
    def export_recent_words(self):
        """导出最近一次的单词"""
        if not self.word_translations:
            self.log_message("⚠️ 没有最近的单词数据可导出", "warning")
            return
        
        # 弹出文件保存对话框
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        file_path = self.get_save_path(
            f"俄语单词卡_最近一次_{timestamp}.txt",
            "保存最近一次的单词卡"
        )
        
        if not file_path:
            self.log_message("❌ 用户取消了保存操作", "warning")
            return
        
        try:
            # 写入TXT文件
            with open(file_path, "w", encoding="utf-8") as f:
                f.write("# 俄语单词卡 - 最近一次处理\n")
                f.write("# 格式: 俄语原形\t中文翻译\n")
                f.write("# 生成时间: " + datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n")
                f.write(f"# 单词总数: {len(self.word_translations)}\n\n")
                
                for word, meaning in self.word_translations:
                    f.write(f"{word}\t{meaning}\n")
            
            self.log_message(f"✅ 已导出最近一次的单词卡: {file_path}", "success")
            self.log_message(f"导出了 {len(self.word_translations)} 个单词", "info")
            
            # 显示成功消息框
            QMessageBox.information(
                self,
                "导出成功",
                f"✅ 已成功导出 {len(self.word_translations)} 个单词到：\n{file_path}"
            )
            
        except Exception as e:
            self.log_message(f"❌ 导出最近一次单词卡失败: {e}", "error")
    
    def export_all_words(self):
        """导出历史所有单词"""
        if not self.word_history:
            self.log_message("⚠️ 单词库为空，没有单词可导出", "warning")
            return
        
        # 弹出文件保存对话框
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        file_path = self.get_save_path(
            f"俄语单词卡_历史所有_{timestamp}.txt",
            "保存历史所有单词卡"
        )
        
        if not file_path:
            self.log_message("❌ 用户取消了保存操作", "warning")
            return
        
        try:
            # 写入TXT文件
            with open(file_path, "w", encoding="utf-8") as f:
                f.write("# 俄语单词卡 - 历史所有单词\n")
                f.write("# 格式: 俄语原形\t中文翻译\n")
                f.write("# 生成时间: " + datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n")
                f.write(f"# 单词总数: {len(self.word_history)}\n\n")
                
                for word, meaning in sorted(self.word_history.items()):
                    f.write(f"{word}\t{meaning}\n")
            
            self.log_message(f"✅ 已导出历史所有单词卡: {file_path}", "success")
            self.log_message(f"导出了 {len(self.word_history)} 个单词", "info")
            
            # 显示成功消息框
            QMessageBox.information(
                self,
                "导出成功",
                f"✅ 已成功导出 {len(self.word_history)} 个单词到：\n{file_path}"
            )
            
        except Exception as e:
            self.log_message(f"❌ 导出历史单词卡失败: {e}", "error")
    
    def export_log_words(self):
        """从日志中提取并导出所有单词"""
        words = self.extract_words_from_log()
        
        if not words:
            self.log_message("⚠️ 日志中没有找到单词翻译数据", "warning")
            return
        
        # 弹出文件保存对话框
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        file_path = self.get_save_path(
            f"俄语单词卡_日志提取_{timestamp}.txt",
            "保存日志中的单词卡"
        )
        
        if not file_path:
            self.log_message("❌ 用户取消了保存操作", "warning")
            return
        
        try:
            # 写入TXT文件
            with open(file_path, "w", encoding="utf-8") as f:
                f.write("# 俄语单词卡 - 从日志中提取\n")
                f.write("# 格式: 俄语原形\t中文翻译\n")
                f.write("# 生成时间: " + datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n")
                f.write(f"# 单词总数: {len(words)}\n\n")
                
                for word, meaning in sorted(words.items()):
                    f.write(f"{word}\t{meaning}\n")
            
            self.log_message(f"✅ 已从日志中导出单词卡: {file_path}", "success")
            self.log_message(f"从日志中提取了 {len(words)} 个单词", "info")
            
            # 显示成功消息框
            QMessageBox.information(
                self,
                "导出成功",
                f"✅ 已成功从日志中导出 {len(words)} 个单词到：\n{file_path}"
            )
            
        except Exception as e:
            self.log_message(f"❌ 导出日志单词卡失败: {e}", "error")
    
    def clear_word_history(self):
        """清空单词历史记录"""
        if not self.word_history:
            self.log_message("⚠️ 单词库已经是空的", "warning")
            return
        
        reply = QMessageBox.question(
            self, "确认清空",
            f"确定要清空单词库吗？\n这将删除 {len(self.word_history)} 个单词记录。",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No
        )
        
        if reply == QMessageBox.Yes:
            self.word_history.clear()
            self.save_word_history()
            self.word_count_label.setText(f"单词库: {len(self.word_history)} 个")
            self.log_message("✅ 单词库已清空", "success")
    
    def start_monitoring(self):
        """开始监控"""
        if self.worker_thread and self.worker_thread.isRunning():
            self.log_message("监控已经在运行", "warning")
            return
        
        # 创建并配置工作线程
        self.worker_thread = WorkerThread()
        self.worker_thread.set_parameters(
            play_times=self.times_spin.value(),
            play_interval=self.play_interval_spin.value(),  # 新增：朗读时间间隔
            check_interval=self.interval_spin.value(),
            process_cooldown=self.cooldown_spin.value(),
            audio_gain_db=self.gain_spin.value(),
            stress_enabled=self.stress_check.isChecked(),
            translation_enabled=self.translation_check.isChecked(),
            morphology_enabled=self.morphology_check.isChecked()
        )
        
        # 连接信号
        self.worker_thread.log_signal.connect(self.log_message)
        self.worker_thread.status_signal.connect(self.update_status)
        self.worker_thread.processed_count_signal.connect(self.update_count)
        self.worker_thread.result_signal.connect(self.update_result)
        self.worker_thread.word_analysis_signal.connect(self.update_word_analysis)  # 新增
        
        # 启动线程
        self.worker_thread.start()
        
        # 更新UI状态
        self.start_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)
        
        # 显示当前设置
        play_times = self.times_spin.value()
        play_interval = self.play_interval_spin.value()
        self.log_message(f"启动剪贴板监控: 朗读{play_times}遍, 间隔{play_interval}秒", "success")
    
    def stop_monitoring(self):
        """停止监控"""
        if self.worker_thread and self.worker_thread.isRunning():
            self.worker_thread.stop()
            self.worker_thread.quit()
            self.worker_thread.wait()
            self.log_message("监控已停止", "info")
        
        # 更新UI状态
        self.start_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)
    
    def clear_log(self):
        """清空日志"""
        self.log_text.clear()
        self.log_messages.clear()
        self.log_message("日志已清空", "info")
    
    def save_log(self):
        """保存日志到文件"""
        try:
            # 弹出文件保存对话框
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            file_path, _ = QFileDialog.getSaveFileName(
                self,
                "保存日志文件",
                os.path.join(os.path.expanduser("~"), f"俄语朗读器日志_{timestamp}.txt"),
                "文本文件 (*.txt);;所有文件 (*.*)"
            )
            
            if not file_path:
                self.log_message("❌ 用户取消了保存操作", "warning")
                return
            
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(self.log_text.toPlainText())
            self.log_message(f"✅ 日志已保存到: {file_path}", "success")
            
            # 显示成功消息框
            QMessageBox.information(
                self,
                "保存成功",
                f"✅ 日志已成功保存到：\n{file_path}"
            )
            
        except Exception as e:
            self.log_message(f"保存日志失败: {e}", "error")
    
    def closeEvent(self, event):
        """窗口关闭事件"""
        if self.worker_thread and self.worker_thread.isRunning():
            reply = QMessageBox.question(
                self, "确认退出",
                "监控正在运行，确定要退出吗？",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )
            
            if reply == QMessageBox.Yes:
                self.stop_monitoring()
                event.accept()
            else:
                event.ignore()
        else:
            event.accept()

def main():
    """主函数"""
    app = QApplication(sys.argv)
    app.setStyle("Fusion")  # 设置现代样式
    
    # 创建并显示主窗口
    window = MainWindow()
    window.show()
    
    # 启动事件循环
    sys.exit(app.exec())

if __name__ == "__main__":
    main()