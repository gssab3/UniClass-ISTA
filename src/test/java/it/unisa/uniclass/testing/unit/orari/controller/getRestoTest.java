package it.unisa.uniclass.testing.unit.orari.controller;

import it.unisa.uniclass.orari.controller.getResto;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.RestoService;
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

@DisplayName("Test per getResto servlet")
class getRestoTest {

    private HttpServletRequest request;
    private HttpServletResponse response;

    private RestoService restoService;
    private getResto servlet;

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

        servlet = new getResto();

        restoService = mock(RestoService.class);
        inject(servlet, "restoService", restoService);

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

        Resto r1 = mock(Resto.class);
        when(r1.getId()).thenReturn(1L);
        when(r1.getNome()).thenReturn("Resto 0");

        Resto r2 = mock(Resto.class);
        when(r2.getId()).thenReturn(2L);
        when(r2.getNome()).thenReturn("Resto 1");

        List<Resto> resti = List.of(r1, r2);

        when(restoService.trovaRestiCorsoLaurea("Informatica"))
                .thenReturn(resti);

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
    // LISTA VUOTA
    // ---------------------------------------------------------

    @Test
    void testDoGetRestiVuoti() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn("Informatica");

        when(restoService.trovaRestiCorsoLaurea("Informatica"))
                .thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        String output = stringWriter.toString().trim();
        assertEquals("[]", output);
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

        verify(restoService, never()).trovaRestiCorsoLaurea(anyString());
    }

    // ---------------------------------------------------------
    // PARAMETRO VUOTO
    // ---------------------------------------------------------

    @Test
    void testParametroVuoto() throws Exception {

        when(request.getParameter("corsoLaurea"))
                .thenReturn("   ");

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
