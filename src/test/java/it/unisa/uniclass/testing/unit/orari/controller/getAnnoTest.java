package it.unisa.uniclass.testing.unit.orari.controller;

import it.unisa.uniclass.orari.controller.getAnno;
import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@DisplayName("Test per getAnno servlet")
class getAnnoTest {

    private HttpServletRequest request;
    private HttpServletResponse response;

    private CorsoLaureaService corsoService;
    private AnnoDidatticoService annoService;

    private getAnno servlet;

    private StringWriter stringWriter;
    private PrintWriter writer;

    private void inject(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @BeforeEach
    void setUp() throws Exception {

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);

        servlet = new getAnno();

        corsoService = mock(CorsoLaureaService.class);
        annoService = mock(AnnoDidatticoService.class);

        inject(servlet, "corsoLaureaService", corsoService);
        inject(servlet, "annoDidatticoService", annoService);

        stringWriter = new StringWriter();
        writer = new PrintWriter(stringWriter);

        when(response.getWriter()).thenReturn(writer);
    }

    // ---------------------------------------------------------
    // FLUSSO COMPLETO
    // ---------------------------------------------------------

    @Test
    void testDoGetFlussoCompleto() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn("Informatica");

        CorsoLaurea corso = mock(CorsoLaurea.class);
        when(corso.getId()).thenReturn(1L);

        when(corsoService.trovaCorsoLaurea("Informatica"))
                .thenReturn(corso);

        AnnoDidattico anno1 = mock(AnnoDidattico.class);
        when(anno1.getId()).thenReturn(1);
        when(anno1.getAnno()).thenReturn("2023-2024");

        AnnoDidattico anno2 = mock(AnnoDidattico.class);
        when(anno2.getId()).thenReturn(2);
        when(anno2.getAnno()).thenReturn("2024-2025");

        List<AnnoDidattico> anni = List.of(anno1, anno2);

        when(annoService.trovaTuttiCorsoLaurea(1L))
                .thenReturn(anni);

        servlet.doGet(request, response);

        String output = stringWriter.toString().trim();

        assertTrue(output.startsWith("["));
        assertTrue(output.endsWith("]"));

        JSONArray array = new JSONArray(output);
        assertEquals(2, array.length());

        JSONObject obj = array.getJSONObject(0);
        assertTrue(obj.has("id"));
        assertTrue(obj.has("nome"));

        verify(response).setContentType("application/json");
        verify(response).setCharacterEncoding("UTF-8");
    }

    // ---------------------------------------------------------
    // ANNI VUOTI
    // ---------------------------------------------------------

    @Test
    void testDoGetAnniVuoti() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn("Informatica");

        CorsoLaurea corso = mock(CorsoLaurea.class);
        when(corso.getId()).thenReturn(1L);

        when(corsoService.trovaCorsoLaurea("Informatica"))
                .thenReturn(corso);

        when(annoService.trovaTuttiCorsoLaurea(1L))
                .thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        String output = stringWriter.toString().trim();
        assertEquals("[]", output);
    }

    // ---------------------------------------------------------
    // CORSO NON TROVATO
    // ---------------------------------------------------------

    @Test
    void testDoGetCorsoNull() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn("Inesistente");

        when(corsoService.trovaCorsoLaurea("Inesistente"))
                .thenReturn(null);

        servlet.doGet(request, response);

        String output = stringWriter.toString().trim();
        assertEquals("[]", output);

        verify(annoService, never()).trovaTuttiCorsoLaurea(anyLong());
    }

    // ---------------------------------------------------------
    // PARAMETRO NULL
    // ---------------------------------------------------------

    @Test
    void testParametroNull() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn(null);

        servlet.doGet(request, response);

        String output = stringWriter.toString().trim();
        assertEquals("[]", output);
    }

    // ---------------------------------------------------------
    // DOPOST DELEGA
    // ---------------------------------------------------------

    @Test
    void testDoPostDelega() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn(null);

        servlet.doPost(request, response);

        String output = stringWriter.toString().trim();
        assertEquals("[]", output);
    }
}
