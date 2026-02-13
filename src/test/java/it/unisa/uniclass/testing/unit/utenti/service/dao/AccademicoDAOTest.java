package it.unisa.uniclass.testing.unit.utenti.service.dao;


import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.service.dao.AccademicoDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class AccademicoDAOTest {

    private void inject(Object target, String field, Object value) throws Exception {
        Field f = target.getClass().getDeclaredField(field);
        f.setAccessible(true);
        f.set(target, value);
    }

    @Test
    void remove_shouldMergeThenRemove_whenNotContained() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        Accademico a = new Accademico();
        Accademico merged = new Accademico();

        when(em.contains(a)).thenReturn(false);
        when(em.merge(a)).thenReturn(merged);

        inject(dao, "em", em);

        dao.remove(a);

        verify(em).merge(a);
        verify(em).remove(merged);
    }

    @Test
    void remove_shouldRemoveDirectly_whenContained() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        Accademico a = new Accademico();

        when(em.contains(a)).thenReturn(true);

        inject(dao, "em", em);

        dao.remove(a);

        verify(em, never()).merge(any());
        verify(em).remove(a);
    }

    @Test
    void findByRole_shouldReturnList() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Accademico> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Accademico.findByRuolo", Accademico.class)).thenReturn(q);
        when(q.setParameter("ruolo", Ruolo.DOCENTE)).thenReturn(q);
        when(q.getResultList()).thenReturn(List.of(new Accademico()));

        inject(dao, "em", em);

        assertEquals(1, dao.findByRole(Ruolo.DOCENTE).size());
    }

    @Test
    void findByRuoloAndDipartimento_shouldReturnList() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Accademico> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Accademico.findByRuoloAndDip", Accademico.class)).thenReturn(q);
        when(q.setParameter("ruolo", Ruolo.DOCENTE)).thenReturn(q);
        when(q.setParameter("dipartimento", "DIEM")).thenReturn(q);
        when(q.getResultList()).thenReturn(List.of(new Accademico()));

        inject(dao, "em", em);

        assertEquals(1, dao.findByRuoloAndDipartimento(Ruolo.DOCENTE, "DIEM").size());
    }

    @Test
    void findAll_shouldReturnList() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Accademico> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Accademico.findAll", Accademico.class)).thenReturn(q);
        when(q.getResultList()).thenReturn(List.of(new Accademico()));

        inject(dao, "em", em);

        assertEquals(1, dao.findAll().size());
    }

    @Test
    void findByMatricola_shouldReturnAccademico() throws Exception {
        AccademicoDAO dao = new AccademicoDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Accademico> q = mock(TypedQuery.class);
        Accademico a = new Accademico();

        when(em.createNamedQuery("Accademico.findByMatricola", Accademico.class)).thenReturn(q);
        when(q.setParameter("matricola", "123")).thenReturn(q);
        when(q.getSingleResult()).thenReturn(a);

        inject(dao, "em", em);

        assertEquals(a, dao.findByMatricola("123"));
    }
}
